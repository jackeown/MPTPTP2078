%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1333+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TbSXtfUpjD

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:30 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  196 (1072 expanded)
%              Number of leaves         :   32 ( 322 expanded)
%              Depth                    :   18
%              Number of atoms          : 2394 (29246 expanded)
%              Number of equality atoms :   48 ( 227 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t56_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( r1_tarski @ ( k2_pre_topc @ A @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v5_pre_topc @ C @ A @ B )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( r1_tarski @ ( k2_pre_topc @ A @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ B @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_tops_2])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
   <= ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ sk_D_1 ) ) @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
   <= ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['1','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
        = X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('16',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      = ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      = ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ( v4_pre_topc @ ( sk_D @ X7 @ X6 @ X8 ) @ X6 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      = ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['18','26'])).

thf('28',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('29',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X32 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X32 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X32 ) ) @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ X32 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ X25 @ ( k2_pre_topc @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      = ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_pre_topc @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
       != X30 )
      | ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) )
       != ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) )
       != ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ ( k2_pre_topc @ X16 @ X17 ) )
        = ( k2_pre_topc @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) )
       != ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ ( sk_D @ X7 @ X6 @ X8 ) ) @ X8 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('75',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80'])).

thf('82',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['72','81'])).

thf('83',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ sk_D_1 ) ) @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['6','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ X25 @ ( k2_pre_topc @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('91',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tarski @ sk_D_1 @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r1_tarski @ sk_D_1 @ ( k2_pre_topc @ sk_B @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('94',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k10_relat_1 @ X24 @ X22 ) @ ( k10_relat_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_D_1 ) @ ( k10_relat_1 @ X0 @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('97',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['84','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_D_1 ) @ ( k10_relat_1 @ X0 @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r1_tarski @ ( k2_pre_topc @ X28 @ X27 ) @ ( k2_pre_topc @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ X1 ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X1 ) ) @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ sk_D_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('113',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['88'])).

thf('114',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('115',plain,
    ( ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('119',plain,
    ( ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_pre_topc @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
       != X30 )
      | ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('123',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) @ sk_B )
      | ( ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
       != ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( v4_pre_topc @ ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) @ sk_B )
      | ( ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
       != ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['88'])).

thf('128',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ ( k2_pre_topc @ X16 @ X17 ) )
        = ( k2_pre_topc @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('129',plain,
    ( ( ( ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) )
        = ( k2_pre_topc @ sk_B @ sk_D_1 ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) )
      = ( k2_pre_topc @ sk_B @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) )
      = ( k2_pre_topc @ sk_B @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('133',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) )
      = ( k2_pre_topc @ sk_B @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('134',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D_1 ) )
      = ( k2_pre_topc @ sk_B @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('135',plain,
    ( ( ( v4_pre_topc @ ( k2_pre_topc @ sk_B @ sk_D_1 ) @ sk_B )
      | ( ( k2_pre_topc @ sk_B @ sk_D_1 )
       != ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','131','132','133','134'])).

thf('136',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('138',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X32 ) ) @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ X32 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['138'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( v4_pre_topc @ X9 @ X6 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['139','147'])).

thf('149',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_B @ sk_D_1 ) @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['137','148'])).

thf('150',plain,
    ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['136','149'])).

thf('151',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['112','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('153',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
        = X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
      = ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['84'])).

thf('159',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['84','96'])).

thf('160',plain,
    ( ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) )
    = ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ),
    inference(simpl_trail,[status(thm)],['157','158','159'])).

thf('161',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k10_relat_1 @ sk_C @ sk_D_1 ) ) @ ( k10_relat_1 @ sk_C @ ( k2_pre_topc @ sk_B @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['108','111','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['87','161'])).


%------------------------------------------------------------------------------
