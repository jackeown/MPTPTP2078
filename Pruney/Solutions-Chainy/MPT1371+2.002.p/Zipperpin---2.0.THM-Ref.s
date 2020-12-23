%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4wazxzxVXe

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:42 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 660 expanded)
%              Number of leaves         :   45 ( 220 expanded)
%              Depth                    :   22
%              Number of atoms          : 1866 (19846 expanded)
%              Number of equality atoms :   66 ( 730 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t26_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( v1_compts_1 @ A )
                  & ( v8_pre_topc @ B )
                  & ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ( v5_pre_topc @ C @ A @ B ) )
               => ( v3_tops_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( v1_compts_1 @ A )
                    & ( v8_pre_topc @ B )
                    & ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ A ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C )
                    & ( v5_pre_topc @ C @ A @ B ) )
                 => ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_compts_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( v4_pre_topc @ D @ A )
                      <=> ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 )
       != ( k2_struct_0 @ X40 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 )
       != ( k2_struct_0 @ X39 ) )
      | ~ ( v2_funct_1 @ X41 )
      | ( m1_subset_1 @ ( sk_D_1 @ X41 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v3_tops_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('18',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6','7','10','13','16','19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( v1_compts_1 @ A )
                  & ( v8_pre_topc @ B )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( v4_pre_topc @ D @ A )
                     => ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v1_compts_1 @ X44 )
      | ~ ( v8_pre_topc @ X43 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 )
       != ( k2_struct_0 @ X43 ) )
      | ~ ( v5_pre_topc @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 @ X46 ) @ X43 )
      | ~ ( v4_pre_topc @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t25_compts_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('40',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','36','37','38','39','40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 )
       != ( k2_struct_0 @ X40 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 )
       != ( k2_struct_0 @ X39 ) )
      | ~ ( v2_funct_1 @ X41 )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 @ ( sk_D_1 @ X41 @ X39 @ X40 ) ) @ X39 )
      | ( v4_pre_topc @ ( sk_D_1 @ X41 @ X39 @ X40 ) @ X40 )
      | ( v3_tops_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('54',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('57',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54','55','56','57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X12 @ X13 @ X11 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v5_pre_topc @ X34 @ X35 @ X33 )
      | ~ ( v4_pre_topc @ X36 @ X33 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) @ X34 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('74',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','78'])).

thf('80',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','79'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('88',plain,(
    ! [X38: $i] :
      ( ( l1_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86','89'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('91',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ( ( k10_relat_1 @ X4 @ ( k9_relat_1 @ X4 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('94',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    = ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['92','95','96','97'])).

thf('99',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('107',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 )
       != ( k2_struct_0 @ X40 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 )
       != ( k2_struct_0 @ X39 ) )
      | ~ ( v2_funct_1 @ X41 )
      | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) @ X41 @ ( sk_D_1 @ X41 @ X39 @ X40 ) ) @ X39 )
      | ~ ( v4_pre_topc @ ( sk_D_1 @ X41 @ X39 @ X40 ) @ X40 )
      | ( v3_tops_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('108',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('116',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','113','114','115','116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['102','103'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['105','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['0','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4wazxzxVXe
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.48/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.67  % Solved by: fo/fo7.sh
% 0.48/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.67  % done 360 iterations in 0.209s
% 0.48/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.67  % SZS output start Refutation
% 0.48/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.48/0.67  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.48/0.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.48/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.67  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.48/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.48/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.67  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.48/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.48/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.48/0.67  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.48/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.67  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.48/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.67  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.48/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.48/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.67  thf(t26_compts_1, conjecture,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.67       ( ![B:$i]:
% 0.48/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.48/0.67             ( l1_pre_topc @ B ) ) =>
% 0.48/0.67           ( ![C:$i]:
% 0.48/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.67                 ( m1_subset_1 @
% 0.48/0.67                   C @ 
% 0.48/0.67                   ( k1_zfmisc_1 @
% 0.48/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.67               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.48/0.67                   ( ( k1_relset_1 @
% 0.48/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.48/0.67                     ( k2_struct_0 @ A ) ) & 
% 0.48/0.67                   ( ( k2_relset_1 @
% 0.48/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.48/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.48/0.67                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.48/0.67                 ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.67    (~( ![A:$i]:
% 0.48/0.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.67          ( ![B:$i]:
% 0.48/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.48/0.67                ( l1_pre_topc @ B ) ) =>
% 0.48/0.67              ( ![C:$i]:
% 0.48/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.67                    ( v1_funct_2 @
% 0.48/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.67                    ( m1_subset_1 @
% 0.48/0.67                      C @ 
% 0.48/0.67                      ( k1_zfmisc_1 @
% 0.48/0.67                        ( k2_zfmisc_1 @
% 0.48/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.67                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.48/0.67                      ( ( k1_relset_1 @
% 0.48/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.48/0.67                        ( k2_struct_0 @ A ) ) & 
% 0.48/0.67                      ( ( k2_relset_1 @
% 0.48/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.48/0.67                        ( k2_struct_0 @ B ) ) & 
% 0.48/0.67                      ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.48/0.67                    ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.48/0.67    inference('cnf.neg', [status(esa)], [t26_compts_1])).
% 0.48/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('1', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(t72_tops_2, axiom,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( l1_pre_topc @ A ) =>
% 0.48/0.67       ( ![B:$i]:
% 0.48/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.48/0.67           ( ![C:$i]:
% 0.48/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.67                 ( m1_subset_1 @
% 0.48/0.67                   C @ 
% 0.48/0.67                   ( k1_zfmisc_1 @
% 0.48/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.67               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.48/0.67                 ( ( ( k1_relset_1 @
% 0.48/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.48/0.67                     ( k2_struct_0 @ A ) ) & 
% 0.48/0.67                   ( ( k2_relset_1 @
% 0.48/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.48/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.48/0.67                   ( v2_funct_1 @ C ) & 
% 0.48/0.67                   ( ![D:$i]:
% 0.48/0.67                     ( ( m1_subset_1 @
% 0.48/0.67                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.67                       ( ( v4_pre_topc @ D @ A ) <=>
% 0.48/0.67                         ( v4_pre_topc @
% 0.48/0.67                           ( k7_relset_1 @
% 0.48/0.67                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.48/0.67                           B ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.67  thf('2', plain,
% 0.48/0.67      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.67         ((v2_struct_0 @ X39)
% 0.48/0.67          | ~ (l1_pre_topc @ X39)
% 0.48/0.67          | ((k1_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ X41)
% 0.48/0.67              != (k2_struct_0 @ X40))
% 0.48/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ X41)
% 0.48/0.67              != (k2_struct_0 @ X39))
% 0.48/0.67          | ~ (v2_funct_1 @ X41)
% 0.48/0.67          | (m1_subset_1 @ (sk_D_1 @ X41 @ X39 @ X40) @ 
% 0.48/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.48/0.67          | (v3_tops_2 @ X41 @ X40 @ X39)
% 0.48/0.67          | ~ (m1_subset_1 @ X41 @ 
% 0.48/0.67               (k1_zfmisc_1 @ 
% 0.48/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39))))
% 0.48/0.67          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39))
% 0.48/0.67          | ~ (v1_funct_1 @ X41)
% 0.48/0.67          | ~ (l1_pre_topc @ X40))),
% 0.48/0.67      inference('cnf', [status(esa)], [t72_tops_2])).
% 0.48/0.67  thf('3', plain,
% 0.48/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.48/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.48/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67            != (k2_struct_0 @ sk_B))
% 0.48/0.67        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67            != (k2_struct_0 @ sk_A))
% 0.48/0.67        | ~ (l1_pre_topc @ sk_B)
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.67  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('6', plain,
% 0.48/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('7', plain, ((v2_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('8', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.48/0.67  thf('9', plain,
% 0.48/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.67         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.48/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.48/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.48/0.67  thf('10', plain,
% 0.48/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k2_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf('11', plain,
% 0.48/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k2_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf('12', plain,
% 0.48/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k2_struct_0 @ sk_B))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('13', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.67  thf('14', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.48/0.67  thf('15', plain,
% 0.48/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.67         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.48/0.67          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.48/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.48/0.67  thf('16', plain,
% 0.48/0.67      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k1_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.67  thf('17', plain,
% 0.48/0.67      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k1_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.67  thf('18', plain,
% 0.48/0.67      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k2_struct_0 @ sk_A))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('19', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.48/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.67  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('21', plain,
% 0.48/0.67      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.48/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.48/0.67        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('demod', [status(thm)],
% 0.48/0.67                ['3', '4', '5', '6', '7', '10', '13', '16', '19', '20'])).
% 0.48/0.67  thf('22', plain,
% 0.48/0.67      (((v2_struct_0 @ sk_B)
% 0.48/0.67        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.48/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.48/0.67      inference('simplify', [status(thm)], ['21'])).
% 0.48/0.67  thf('23', plain, (~ (v2_struct_0 @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('24', plain,
% 0.48/0.67      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.48/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.67      inference('clc', [status(thm)], ['22', '23'])).
% 0.48/0.67  thf('25', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('26', plain,
% 0.48/0.67      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.48/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.67      inference('clc', [status(thm)], ['24', '25'])).
% 0.48/0.67  thf('27', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(t25_compts_1, axiom,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.67       ( ![B:$i]:
% 0.48/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.48/0.67             ( l1_pre_topc @ B ) ) =>
% 0.48/0.67           ( ![C:$i]:
% 0.48/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.67                 ( m1_subset_1 @
% 0.48/0.67                   C @ 
% 0.48/0.67                   ( k1_zfmisc_1 @
% 0.48/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.67               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.48/0.67                   ( ( k2_relset_1 @
% 0.48/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.48/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.48/0.67                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.48/0.67                 ( ![D:$i]:
% 0.48/0.67                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.67                     ( ( v4_pre_topc @ D @ A ) =>
% 0.48/0.67                       ( v4_pre_topc @
% 0.48/0.67                         ( k7_relset_1 @
% 0.48/0.67                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.48/0.67                         B ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.67  thf('28', plain,
% 0.48/0.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.48/0.67         ((v2_struct_0 @ X43)
% 0.48/0.67          | ~ (v2_pre_topc @ X43)
% 0.48/0.67          | ~ (l1_pre_topc @ X43)
% 0.48/0.67          | ~ (v1_compts_1 @ X44)
% 0.48/0.67          | ~ (v8_pre_topc @ X43)
% 0.48/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45)
% 0.48/0.67              != (k2_struct_0 @ X43))
% 0.48/0.67          | ~ (v5_pre_topc @ X45 @ X44 @ X43)
% 0.48/0.67          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.48/0.67          | (v4_pre_topc @ 
% 0.48/0.67             (k7_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45 @ 
% 0.48/0.67              X46) @ 
% 0.48/0.67             X43)
% 0.48/0.67          | ~ (v4_pre_topc @ X46 @ X44)
% 0.48/0.67          | ~ (m1_subset_1 @ X45 @ 
% 0.48/0.67               (k1_zfmisc_1 @ 
% 0.48/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))))
% 0.48/0.67          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))
% 0.48/0.67          | ~ (v1_funct_1 @ X45)
% 0.48/0.67          | ~ (l1_pre_topc @ X44)
% 0.48/0.67          | ~ (v2_pre_topc @ X44))),
% 0.48/0.67      inference('cnf', [status(esa)], [t25_compts_1])).
% 0.48/0.67  thf('29', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (v2_pre_topc @ sk_A)
% 0.48/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.48/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.48/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.48/0.67          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.48/0.67          | (v4_pre_topc @ 
% 0.48/0.67             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.67              sk_C @ X0) @ 
% 0.48/0.67             sk_B)
% 0.48/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.48/0.67          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67              != (k2_struct_0 @ sk_B))
% 0.48/0.67          | ~ (v8_pre_topc @ sk_B)
% 0.48/0.67          | ~ (v1_compts_1 @ sk_A)
% 0.48/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.48/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.48/0.67          | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.67  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('33', plain,
% 0.48/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('34', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(redefinition_k7_relset_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.67       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.48/0.67  thf('35', plain,
% 0.48/0.67      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.67         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.48/0.67          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.48/0.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.48/0.67  thf('36', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.48/0.67           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.67  thf('37', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('38', plain,
% 0.48/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k2_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.67  thf('40', plain, ((v8_pre_topc @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('41', plain, ((v1_compts_1 @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('44', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.48/0.67          | (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B)
% 0.48/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.67          | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.48/0.67          | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('demod', [status(thm)],
% 0.48/0.67                ['29', '30', '31', '32', '33', '36', '37', '38', '39', '40', 
% 0.48/0.67                 '41', '42', '43'])).
% 0.48/0.67  thf('45', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((v2_struct_0 @ sk_B)
% 0.48/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.67          | (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B)
% 0.48/0.67          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.48/0.67      inference('simplify', [status(thm)], ['44'])).
% 0.48/0.67  thf('46', plain,
% 0.48/0.67      ((~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67           sk_B)
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup-', [status(thm)], ['26', '45'])).
% 0.48/0.67  thf('47', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('48', plain,
% 0.48/0.67      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.67         ((v2_struct_0 @ X39)
% 0.48/0.67          | ~ (l1_pre_topc @ X39)
% 0.48/0.67          | ((k1_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ X41)
% 0.48/0.67              != (k2_struct_0 @ X40))
% 0.48/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ X41)
% 0.48/0.67              != (k2_struct_0 @ X39))
% 0.48/0.67          | ~ (v2_funct_1 @ X41)
% 0.48/0.67          | (v4_pre_topc @ 
% 0.48/0.67             (k7_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ X41 @ 
% 0.48/0.67              (sk_D_1 @ X41 @ X39 @ X40)) @ 
% 0.48/0.67             X39)
% 0.48/0.67          | (v4_pre_topc @ (sk_D_1 @ X41 @ X39 @ X40) @ X40)
% 0.48/0.67          | (v3_tops_2 @ X41 @ X40 @ X39)
% 0.48/0.67          | ~ (m1_subset_1 @ X41 @ 
% 0.48/0.67               (k1_zfmisc_1 @ 
% 0.48/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39))))
% 0.48/0.67          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39))
% 0.48/0.67          | ~ (v1_funct_1 @ X41)
% 0.48/0.67          | ~ (l1_pre_topc @ X40))),
% 0.48/0.67      inference('cnf', [status(esa)], [t72_tops_2])).
% 0.48/0.67  thf('49', plain,
% 0.48/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v4_pre_topc @ 
% 0.48/0.67           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.48/0.67            (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67           sk_B)
% 0.48/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.48/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67            != (k2_struct_0 @ sk_B))
% 0.48/0.67        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67            != (k2_struct_0 @ sk_A))
% 0.48/0.67        | ~ (l1_pre_topc @ sk_B)
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.67  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('52', plain,
% 0.48/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('53', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.48/0.67           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.67  thf('54', plain, ((v2_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('55', plain,
% 0.48/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k2_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf('56', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.67  thf('57', plain,
% 0.48/0.67      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k1_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.67  thf('58', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.48/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.67  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('60', plain,
% 0.48/0.67      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67           sk_B)
% 0.48/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.48/0.67        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('demod', [status(thm)],
% 0.48/0.67                ['49', '50', '51', '52', '53', '54', '55', '56', '57', '58', 
% 0.48/0.67                 '59'])).
% 0.48/0.67  thf('61', plain,
% 0.48/0.67      (((v2_struct_0 @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67           sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.48/0.67      inference('simplify', [status(thm)], ['60'])).
% 0.48/0.67  thf('62', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(dt_k7_relset_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.67       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.48/0.67  thf('63', plain,
% 0.48/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.48/0.67          | (m1_subset_1 @ (k7_relset_1 @ X12 @ X13 @ X11 @ X14) @ 
% 0.48/0.67             (k1_zfmisc_1 @ X13)))),
% 0.48/0.67      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.48/0.67  thf('64', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (m1_subset_1 @ 
% 0.48/0.67          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.48/0.67           X0) @ 
% 0.48/0.67          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.67  thf('65', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.48/0.67           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.67  thf('66', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (m1_subset_1 @ (k9_relat_1 @ sk_C @ X0) @ 
% 0.48/0.67          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.48/0.67      inference('demod', [status(thm)], ['64', '65'])).
% 0.48/0.67  thf('67', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(d12_pre_topc, axiom,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( l1_pre_topc @ A ) =>
% 0.48/0.67       ( ![B:$i]:
% 0.48/0.67         ( ( l1_pre_topc @ B ) =>
% 0.48/0.67           ( ![C:$i]:
% 0.48/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.67                 ( m1_subset_1 @
% 0.48/0.67                   C @ 
% 0.48/0.67                   ( k1_zfmisc_1 @
% 0.48/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.67               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.48/0.67                 ( ![D:$i]:
% 0.48/0.67                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.48/0.67                     ( ( v4_pre_topc @ D @ B ) =>
% 0.48/0.67                       ( v4_pre_topc @
% 0.48/0.67                         ( k8_relset_1 @
% 0.48/0.67                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.48/0.67                         A ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.67  thf('68', plain,
% 0.48/0.67      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.48/0.67         (~ (l1_pre_topc @ X33)
% 0.48/0.67          | ~ (v5_pre_topc @ X34 @ X35 @ X33)
% 0.48/0.67          | ~ (v4_pre_topc @ X36 @ X33)
% 0.48/0.67          | (v4_pre_topc @ 
% 0.48/0.67             (k8_relset_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ X34 @ 
% 0.48/0.67              X36) @ 
% 0.48/0.67             X35)
% 0.48/0.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.48/0.67          | ~ (m1_subset_1 @ X34 @ 
% 0.48/0.67               (k1_zfmisc_1 @ 
% 0.48/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 0.48/0.67          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 0.48/0.67          | ~ (v1_funct_1 @ X34)
% 0.48/0.67          | ~ (l1_pre_topc @ X35))),
% 0.48/0.67      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.48/0.67  thf('69', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (l1_pre_topc @ sk_A)
% 0.48/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.48/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.48/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.48/0.67          | (v4_pre_topc @ 
% 0.48/0.67             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.67              sk_C @ X0) @ 
% 0.48/0.67             sk_A)
% 0.48/0.67          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.48/0.67          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.48/0.67          | ~ (l1_pre_topc @ sk_B))),
% 0.48/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.48/0.67  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('72', plain,
% 0.48/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('73', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(redefinition_k8_relset_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.67       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.48/0.67  thf('74', plain,
% 0.48/0.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.48/0.67         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.48/0.67          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.48/0.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.48/0.67  thf('75', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.48/0.67           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['73', '74'])).
% 0.48/0.67  thf('76', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('78', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.48/0.67          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.48/0.67          | ~ (v4_pre_topc @ X0 @ sk_B))),
% 0.48/0.67      inference('demod', [status(thm)],
% 0.48/0.67                ['69', '70', '71', '72', '75', '76', '77'])).
% 0.48/0.67  thf('79', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B)
% 0.48/0.67          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) @ 
% 0.48/0.67             sk_A))),
% 0.48/0.67      inference('sup-', [status(thm)], ['66', '78'])).
% 0.48/0.67  thf('80', plain,
% 0.48/0.67      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v2_struct_0 @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ 
% 0.48/0.67           (k10_relat_1 @ sk_C @ 
% 0.48/0.67            (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))) @ 
% 0.48/0.67           sk_A))),
% 0.48/0.67      inference('sup-', [status(thm)], ['61', '79'])).
% 0.48/0.67  thf(d3_struct_0, axiom,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.48/0.67  thf('81', plain,
% 0.48/0.67      (![X37 : $i]:
% 0.48/0.67         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.48/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.48/0.67  thf('82', plain,
% 0.48/0.67      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.48/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.67      inference('clc', [status(thm)], ['24', '25'])).
% 0.48/0.67  thf(t3_subset, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.67  thf('83', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.67  thf('84', plain,
% 0.48/0.67      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.48/0.67      inference('sup-', [status(thm)], ['82', '83'])).
% 0.48/0.67  thf('85', plain,
% 0.48/0.67      (((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.48/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.48/0.67      inference('sup+', [status(thm)], ['81', '84'])).
% 0.48/0.67  thf('86', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.48/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.67  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(dt_l1_pre_topc, axiom,
% 0.48/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.48/0.67  thf('88', plain,
% 0.48/0.67      (![X38 : $i]: ((l1_struct_0 @ X38) | ~ (l1_pre_topc @ X38))),
% 0.48/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.48/0.67  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.48/0.67      inference('sup-', [status(thm)], ['87', '88'])).
% 0.48/0.67  thf('90', plain,
% 0.48/0.67      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (k1_relat_1 @ sk_C))),
% 0.48/0.67      inference('demod', [status(thm)], ['85', '86', '89'])).
% 0.48/0.67  thf(t164_funct_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.48/0.67       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.48/0.67         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.48/0.67  thf('91', plain,
% 0.48/0.67      (![X3 : $i, X4 : $i]:
% 0.48/0.67         (~ (r1_tarski @ X3 @ (k1_relat_1 @ X4))
% 0.48/0.67          | ~ (v2_funct_1 @ X4)
% 0.48/0.67          | ((k10_relat_1 @ X4 @ (k9_relat_1 @ X4 @ X3)) = (X3))
% 0.48/0.67          | ~ (v1_funct_1 @ X4)
% 0.48/0.67          | ~ (v1_relat_1 @ X4))),
% 0.48/0.67      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.48/0.67  thf('92', plain,
% 0.48/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.48/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.67        | ((k10_relat_1 @ sk_C @ 
% 0.48/0.67            (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.48/0.67            = (sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.48/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['90', '91'])).
% 0.48/0.67  thf('93', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(cc1_relset_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.67       ( v1_relat_1 @ C ) ))).
% 0.48/0.67  thf('94', plain,
% 0.48/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.48/0.67         ((v1_relat_1 @ X5)
% 0.48/0.67          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.48/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.67  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 0.48/0.67      inference('sup-', [status(thm)], ['93', '94'])).
% 0.48/0.67  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('98', plain,
% 0.48/0.67      (((k10_relat_1 @ sk_C @ 
% 0.48/0.67         (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.48/0.67         = (sk_D_1 @ sk_C @ sk_B @ sk_A))),
% 0.48/0.67      inference('demod', [status(thm)], ['92', '95', '96', '97'])).
% 0.48/0.67  thf('99', plain,
% 0.48/0.67      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v2_struct_0 @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.48/0.67      inference('demod', [status(thm)], ['80', '98'])).
% 0.48/0.67  thf('100', plain,
% 0.48/0.67      (((v2_struct_0 @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.48/0.67      inference('simplify', [status(thm)], ['99'])).
% 0.48/0.67  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('102', plain,
% 0.48/0.67      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.48/0.67      inference('clc', [status(thm)], ['100', '101'])).
% 0.48/0.67  thf('103', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('104', plain, ((v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.48/0.67      inference('clc', [status(thm)], ['102', '103'])).
% 0.48/0.67  thf('105', plain,
% 0.48/0.67      (((v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67         sk_B)
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('demod', [status(thm)], ['46', '104'])).
% 0.48/0.67  thf('106', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.48/0.67           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.67  thf('107', plain,
% 0.48/0.67      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.67         ((v2_struct_0 @ X39)
% 0.48/0.67          | ~ (l1_pre_topc @ X39)
% 0.48/0.67          | ((k1_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ X41)
% 0.48/0.67              != (k2_struct_0 @ X40))
% 0.48/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ X41)
% 0.48/0.67              != (k2_struct_0 @ X39))
% 0.48/0.67          | ~ (v2_funct_1 @ X41)
% 0.48/0.67          | ~ (v4_pre_topc @ 
% 0.48/0.67               (k7_relset_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39) @ 
% 0.48/0.67                X41 @ (sk_D_1 @ X41 @ X39 @ X40)) @ 
% 0.48/0.67               X39)
% 0.48/0.67          | ~ (v4_pre_topc @ (sk_D_1 @ X41 @ X39 @ X40) @ X40)
% 0.48/0.67          | (v3_tops_2 @ X41 @ X40 @ X39)
% 0.48/0.67          | ~ (m1_subset_1 @ X41 @ 
% 0.48/0.67               (k1_zfmisc_1 @ 
% 0.48/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39))))
% 0.48/0.67          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39))
% 0.48/0.67          | ~ (v1_funct_1 @ X41)
% 0.48/0.67          | ~ (l1_pre_topc @ X40))),
% 0.48/0.67      inference('cnf', [status(esa)], [t72_tops_2])).
% 0.48/0.67  thf('108', plain,
% 0.48/0.67      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67           sk_B)
% 0.48/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.48/0.67        | ~ (m1_subset_1 @ sk_C @ 
% 0.48/0.67             (k1_zfmisc_1 @ 
% 0.48/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.48/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67            != (k2_struct_0 @ sk_B))
% 0.48/0.67        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67            != (k2_struct_0 @ sk_A))
% 0.48/0.67        | ~ (l1_pre_topc @ sk_B)
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup-', [status(thm)], ['106', '107'])).
% 0.48/0.67  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('111', plain,
% 0.48/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('112', plain,
% 0.48/0.67      ((m1_subset_1 @ sk_C @ 
% 0.48/0.67        (k1_zfmisc_1 @ 
% 0.48/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('114', plain,
% 0.48/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k2_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.48/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.67  thf('116', plain,
% 0.48/0.67      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.48/0.67         = (k1_relat_1 @ sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.67  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.48/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.67  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('119', plain,
% 0.48/0.67      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67           sk_B)
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.48/0.67        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.48/0.67        | (v2_struct_0 @ sk_B))),
% 0.48/0.67      inference('demod', [status(thm)],
% 0.48/0.67                ['108', '109', '110', '111', '112', '113', '114', '115', 
% 0.48/0.67                 '116', '117', '118'])).
% 0.48/0.67  thf('120', plain,
% 0.48/0.67      (((v2_struct_0 @ sk_B)
% 0.48/0.67        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | ~ (v4_pre_topc @ 
% 0.48/0.67             (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ sk_B))),
% 0.48/0.67      inference('simplify', [status(thm)], ['119'])).
% 0.48/0.67  thf('121', plain, ((v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.48/0.67      inference('clc', [status(thm)], ['102', '103'])).
% 0.48/0.67  thf('122', plain,
% 0.48/0.67      (((v2_struct_0 @ sk_B)
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.48/0.67        | ~ (v4_pre_topc @ 
% 0.48/0.67             (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ sk_B))),
% 0.48/0.67      inference('demod', [status(thm)], ['120', '121'])).
% 0.48/0.67  thf('123', plain, (~ (v2_struct_0 @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('124', plain,
% 0.48/0.67      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67           sk_B)
% 0.48/0.67        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.48/0.67      inference('clc', [status(thm)], ['122', '123'])).
% 0.48/0.67  thf('125', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('126', plain,
% 0.48/0.67      (~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.48/0.67          sk_B)),
% 0.48/0.67      inference('clc', [status(thm)], ['124', '125'])).
% 0.48/0.67  thf('127', plain, ((v2_struct_0 @ sk_B)),
% 0.48/0.67      inference('clc', [status(thm)], ['105', '126'])).
% 0.48/0.67  thf('128', plain, ($false), inference('demod', [status(thm)], ['0', '127'])).
% 0.48/0.67  
% 0.48/0.67  % SZS output end Refutation
% 0.48/0.67  
% 0.48/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
