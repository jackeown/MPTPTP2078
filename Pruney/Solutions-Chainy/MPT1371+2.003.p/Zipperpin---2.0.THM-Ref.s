%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tuWoRyMdom

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:42 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 529 expanded)
%              Number of leaves         :   43 ( 179 expanded)
%              Depth                    :   21
%              Number of atoms          : 1843 (16333 expanded)
%              Number of equality atoms :   58 ( 561 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 )
       != ( k2_struct_0 @ X34 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 )
       != ( k2_struct_0 @ X33 ) )
      | ~ ( v2_funct_1 @ X35 )
      | ( m1_subset_1 @ ( sk_D_1 @ X35 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v3_tops_2 @ X35 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6','7','8','9','10'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_compts_1 @ X38 )
      | ~ ( v8_pre_topc @ X37 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) @ X39 )
       != ( k2_struct_0 @ X37 ) )
      | ~ ( v5_pre_topc @ X39 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) @ X39 @ X40 ) @ X37 )
      | ~ ( v4_pre_topc @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t25_compts_1])).

thf('19',plain,(
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
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','26','27','28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 )
       != ( k2_struct_0 @ X34 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 )
       != ( k2_struct_0 @ X33 ) )
      | ~ ( v2_funct_1 @ X35 )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 @ ( sk_D_1 @ X35 @ X33 @ X34 ) ) @ X33 )
      | ( v4_pre_topc @ ( sk_D_1 @ X35 @ X33 @ X34 ) @ X34 )
      | ( v3_tops_2 @ X35 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('38',plain,
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40','41','42','43','44','45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('58',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('62',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v5_pre_topc @ X28 @ X29 @ X27 )
      | ~ ( v4_pre_topc @ X30 @ X27 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ X3 ) @ X0 )
      | ~ ( v4_pre_topc @ X3 @ X1 )
      | ~ ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','69','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','74'])).

thf('76',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','75'])).

thf('77',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('83',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ( ( k10_relat_1 @ X4 @ ( k9_relat_1 @ X4 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('92',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['90','93','94','95'])).

thf('97',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    = ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','96'])).

thf('98',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('106',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 )
       != ( k2_struct_0 @ X34 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 )
       != ( k2_struct_0 @ X33 ) )
      | ~ ( v2_funct_1 @ X35 )
      | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X35 @ ( sk_D_1 @ X35 @ X33 @ X34 ) ) @ X33 )
      | ~ ( v4_pre_topc @ ( sk_D_1 @ X35 @ X33 @ X34 ) @ X34 )
      | ( v3_tops_2 @ X35 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('107',plain,
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
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['101','102'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108','109','110','111','112','113','114','115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['104','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tuWoRyMdom
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 232 iterations in 0.093s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.36/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.36/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.56  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.36/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(t26_compts_1, conjecture,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.56             ( l1_pre_topc @ B ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.56                 ( m1_subset_1 @
% 0.36/0.56                   C @ 
% 0.36/0.56                   ( k1_zfmisc_1 @
% 0.36/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.56               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.36/0.56                   ( ( k1_relset_1 @
% 0.36/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.56                     ( k2_struct_0 @ A ) ) & 
% 0.36/0.56                   ( ( k2_relset_1 @
% 0.36/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.56                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.36/0.56                 ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i]:
% 0.36/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56          ( ![B:$i]:
% 0.36/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.56                ( l1_pre_topc @ B ) ) =>
% 0.36/0.56              ( ![C:$i]:
% 0.36/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.56                    ( v1_funct_2 @
% 0.36/0.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.56                    ( m1_subset_1 @
% 0.36/0.56                      C @ 
% 0.36/0.56                      ( k1_zfmisc_1 @
% 0.36/0.56                        ( k2_zfmisc_1 @
% 0.36/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.56                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.36/0.56                      ( ( k1_relset_1 @
% 0.36/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.56                        ( k2_struct_0 @ A ) ) & 
% 0.36/0.56                      ( ( k2_relset_1 @
% 0.36/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.56                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.56                      ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.36/0.56                    ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t26_compts_1])).
% 0.36/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t72_tops_2, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.56                 ( m1_subset_1 @
% 0.36/0.56                   C @ 
% 0.36/0.56                   ( k1_zfmisc_1 @
% 0.36/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.56               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.36/0.56                 ( ( ( k1_relset_1 @
% 0.36/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.56                     ( k2_struct_0 @ A ) ) & 
% 0.36/0.56                   ( ( k2_relset_1 @
% 0.36/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.56                   ( v2_funct_1 @ C ) & 
% 0.36/0.56                   ( ![D:$i]:
% 0.36/0.56                     ( ( m1_subset_1 @
% 0.36/0.56                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                       ( ( v4_pre_topc @ D @ A ) <=>
% 0.36/0.56                         ( v4_pre_topc @
% 0.36/0.56                           ( k7_relset_1 @
% 0.36/0.56                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.36/0.56                           B ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X33)
% 0.36/0.56          | ~ (l1_pre_topc @ X33)
% 0.36/0.56          | ((k1_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35)
% 0.36/0.56              != (k2_struct_0 @ X34))
% 0.36/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35)
% 0.36/0.56              != (k2_struct_0 @ X33))
% 0.36/0.56          | ~ (v2_funct_1 @ X35)
% 0.36/0.56          | (m1_subset_1 @ (sk_D_1 @ X35 @ X33 @ X34) @ 
% 0.36/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.36/0.56          | (v3_tops_2 @ X35 @ X34 @ X33)
% 0.36/0.56          | ~ (m1_subset_1 @ X35 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.36/0.56          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.36/0.56          | ~ (v1_funct_1 @ X35)
% 0.36/0.56          | ~ (l1_pre_topc @ X34))),
% 0.36/0.56      inference('cnf', [status(esa)], [t72_tops_2])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56            != (k2_struct_0 @ sk_B))
% 0.36/0.56        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56            != (k2_struct_0 @ sk_A))
% 0.36/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('7', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.36/0.56        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)],
% 0.36/0.56                ['3', '4', '5', '6', '7', '8', '9', '10'])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B)
% 0.36/0.56        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.56  thf('13', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('clc', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('15', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.36/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('clc', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t25_compts_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.56             ( l1_pre_topc @ B ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.56                 ( m1_subset_1 @
% 0.36/0.56                   C @ 
% 0.36/0.56                   ( k1_zfmisc_1 @
% 0.36/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.56               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.36/0.56                   ( ( k2_relset_1 @
% 0.36/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.56                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.36/0.56                 ( ![D:$i]:
% 0.36/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                     ( ( v4_pre_topc @ D @ A ) =>
% 0.36/0.56                       ( v4_pre_topc @
% 0.36/0.56                         ( k7_relset_1 @
% 0.36/0.56                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.36/0.56                         B ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X37)
% 0.36/0.56          | ~ (v2_pre_topc @ X37)
% 0.36/0.56          | ~ (l1_pre_topc @ X37)
% 0.36/0.56          | ~ (v1_compts_1 @ X38)
% 0.36/0.56          | ~ (v8_pre_topc @ X37)
% 0.36/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37) @ X39)
% 0.36/0.56              != (k2_struct_0 @ X37))
% 0.36/0.56          | ~ (v5_pre_topc @ X39 @ X38 @ X37)
% 0.36/0.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.36/0.56          | (v4_pre_topc @ 
% 0.36/0.56             (k7_relset_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37) @ X39 @ 
% 0.36/0.56              X40) @ 
% 0.36/0.56             X37)
% 0.36/0.56          | ~ (v4_pre_topc @ X40 @ X38)
% 0.36/0.56          | ~ (m1_subset_1 @ X39 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))))
% 0.36/0.56          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X37))
% 0.36/0.56          | ~ (v1_funct_1 @ X39)
% 0.36/0.56          | ~ (l1_pre_topc @ X38)
% 0.36/0.56          | ~ (v2_pre_topc @ X38))),
% 0.36/0.56      inference('cnf', [status(esa)], [t25_compts_1])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.56          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.56          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (v4_pre_topc @ 
% 0.36/0.56             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.56              sk_C @ X0) @ 
% 0.36/0.56             sk_B)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.36/0.56          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56              != (k2_struct_0 @ sk_B))
% 0.36/0.56          | ~ (v8_pre_topc @ sk_B)
% 0.36/0.56          | ~ (v1_compts_1 @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.56  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.36/0.56          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.56           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf('27', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('29', plain, ((v8_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('30', plain, ((v1_compts_1 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('32', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.36/0.56          | (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.36/0.56          | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)],
% 0.36/0.56                ['19', '20', '21', '22', '23', '26', '27', '28', '29', '30', 
% 0.36/0.56                 '31', '32'])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_B)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B)
% 0.36/0.56          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.36/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      ((~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56           sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['16', '34'])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X33)
% 0.36/0.56          | ~ (l1_pre_topc @ X33)
% 0.36/0.56          | ((k1_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35)
% 0.36/0.56              != (k2_struct_0 @ X34))
% 0.36/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35)
% 0.36/0.56              != (k2_struct_0 @ X33))
% 0.36/0.56          | ~ (v2_funct_1 @ X35)
% 0.36/0.56          | (v4_pre_topc @ 
% 0.36/0.56             (k7_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35 @ 
% 0.36/0.56              (sk_D_1 @ X35 @ X33 @ X34)) @ 
% 0.36/0.56             X33)
% 0.36/0.56          | (v4_pre_topc @ (sk_D_1 @ X35 @ X33 @ X34) @ X34)
% 0.36/0.56          | (v3_tops_2 @ X35 @ X34 @ X33)
% 0.36/0.56          | ~ (m1_subset_1 @ X35 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.36/0.56          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.36/0.56          | ~ (v1_funct_1 @ X35)
% 0.36/0.56          | ~ (l1_pre_topc @ X34))),
% 0.36/0.56      inference('cnf', [status(esa)], [t72_tops_2])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | (v4_pre_topc @ 
% 0.36/0.56           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.56            (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56           sk_B)
% 0.36/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56            != (k2_struct_0 @ sk_B))
% 0.36/0.56        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56            != (k2_struct_0 @ sk_A))
% 0.36/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.56  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.56           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf('43', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56           sk_B)
% 0.36/0.56        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.36/0.56        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)],
% 0.36/0.56                ['38', '39', '40', '41', '42', '43', '44', '45', '46'])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56           sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.56      inference('simplify', [status(thm)], ['47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(dt_k7_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.36/0.56          | (m1_subset_1 @ (k7_relset_1 @ X9 @ X10 @ X8 @ X11) @ 
% 0.36/0.56             (k1_zfmisc_1 @ X10)))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (m1_subset_1 @ 
% 0.36/0.56          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.56           X0) @ 
% 0.36/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.56           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (m1_subset_1 @ (k9_relat_1 @ sk_C @ X0) @ 
% 0.36/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.36/0.56  thf(d3_struct_0, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      (![X31 : $i]:
% 0.36/0.56         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('56', plain,
% 0.36/0.56      (((m1_subset_1 @ sk_C @ 
% 0.36/0.56         (k1_zfmisc_1 @ 
% 0.36/0.56          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.36/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup+', [status(thm)], ['54', '55'])).
% 0.36/0.56  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(dt_l1_pre_topc, axiom,
% 0.36/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.56  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('demod', [status(thm)], ['56', '59'])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (![X31 : $i]:
% 0.36/0.56         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.56  thf(d12_pre_topc, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( l1_pre_topc @ B ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.56                 ( m1_subset_1 @
% 0.36/0.56                   C @ 
% 0.36/0.56                   ( k1_zfmisc_1 @
% 0.36/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.56               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.36/0.56                 ( ![D:$i]:
% 0.36/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.56                     ( ( v4_pre_topc @ D @ B ) =>
% 0.36/0.56                       ( v4_pre_topc @
% 0.36/0.56                         ( k8_relset_1 @
% 0.36/0.56                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.36/0.56                         A ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X27)
% 0.36/0.56          | ~ (v5_pre_topc @ X28 @ X29 @ X27)
% 0.36/0.56          | ~ (v4_pre_topc @ X30 @ X27)
% 0.36/0.56          | (v4_pre_topc @ 
% 0.36/0.56             (k8_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28 @ 
% 0.36/0.56              X30) @ 
% 0.36/0.56             X29)
% 0.36/0.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.36/0.56          | ~ (m1_subset_1 @ X28 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 0.36/0.56          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 0.36/0.56          | ~ (v1_funct_1 @ X28)
% 0.36/0.56          | ~ (l1_pre_topc @ X29))),
% 0.36/0.56      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X2 @ 
% 0.36/0.56             (k1_zfmisc_1 @ 
% 0.36/0.56              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.36/0.56          | ~ (l1_struct_0 @ X0)
% 0.36/0.56          | ~ (l1_pre_topc @ X0)
% 0.36/0.56          | ~ (v1_funct_1 @ X2)
% 0.36/0.56          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.36/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.36/0.56          | (v4_pre_topc @ 
% 0.36/0.56             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ X3) @ 
% 0.36/0.56             X0)
% 0.36/0.56          | ~ (v4_pre_topc @ X3 @ X1)
% 0.36/0.56          | ~ (v5_pre_topc @ X2 @ X0 @ X1)
% 0.36/0.56          | ~ (l1_pre_topc @ X1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ sk_B)
% 0.36/0.56          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.36/0.56          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.36/0.56          | (v4_pre_topc @ 
% 0.36/0.56             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.56              sk_C @ X0) @ 
% 0.36/0.56             sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.56          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['60', '63'])).
% 0.36/0.56  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('66', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.36/0.56          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.56           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v4_pre_topc @ X0 @ sk_B)
% 0.36/0.56          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('demod', [status(thm)],
% 0.36/0.56                ['64', '65', '66', '69', '70', '71', '72', '73'])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v4_pre_topc @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) @ sk_A)
% 0.36/0.56          | ~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['53', '74'])).
% 0.36/0.56  thf('76', plain,
% 0.36/0.56      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | (v2_struct_0 @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ 
% 0.36/0.56           (k10_relat_1 @ sk_C @ 
% 0.36/0.56            (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.56           sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['48', '75'])).
% 0.36/0.56  thf('77', plain,
% 0.36/0.56      (![X31 : $i]:
% 0.36/0.56         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.56  thf('78', plain,
% 0.36/0.56      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.36/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('clc', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf(t3_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.56  thf('79', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('80', plain,
% 0.36/0.56      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      (((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.36/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup+', [status(thm)], ['77', '80'])).
% 0.36/0.56  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('83', plain,
% 0.36/0.56      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.36/0.56  thf('84', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.56         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.36/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.56  thf('86', plain,
% 0.36/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k1_relat_1 @ sk_C))),
% 0.36/0.56      inference('sup-', [status(thm)], ['84', '85'])).
% 0.36/0.56  thf('87', plain,
% 0.36/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('88', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup+', [status(thm)], ['86', '87'])).
% 0.36/0.56  thf(t164_funct_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.56       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.36/0.56         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ (k1_relat_1 @ X4))
% 0.36/0.56          | ~ (v2_funct_1 @ X4)
% 0.36/0.56          | ((k10_relat_1 @ X4 @ (k9_relat_1 @ X4 @ X3)) = (X3))
% 0.36/0.56          | ~ (v1_funct_1 @ X4)
% 0.36/0.56          | ~ (v1_relat_1 @ X4))),
% 0.36/0.56      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.36/0.56  thf('90', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v1_relat_1 @ sk_C)
% 0.36/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.56          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.36/0.56          | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.36/0.56  thf('91', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(cc1_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( v1_relat_1 @ C ) ))).
% 0.36/0.56  thf('92', plain,
% 0.36/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.56         ((v1_relat_1 @ X5)
% 0.36/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.56  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.56      inference('sup-', [status(thm)], ['91', '92'])).
% 0.36/0.56  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('96', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_A))
% 0.36/0.56          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['90', '93', '94', '95'])).
% 0.36/0.56  thf('97', plain,
% 0.36/0.56      (((k10_relat_1 @ sk_C @ 
% 0.36/0.56         (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 0.36/0.56         = (sk_D_1 @ sk_C @ sk_B @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['83', '96'])).
% 0.36/0.56  thf('98', plain,
% 0.36/0.56      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | (v2_struct_0 @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['76', '97'])).
% 0.36/0.56  thf('99', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.56      inference('simplify', [status(thm)], ['98'])).
% 0.36/0.56  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('101', plain,
% 0.36/0.56      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.36/0.56      inference('clc', [status(thm)], ['99', '100'])).
% 0.36/0.56  thf('102', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('103', plain, ((v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.36/0.56      inference('clc', [status(thm)], ['101', '102'])).
% 0.36/0.56  thf('104', plain,
% 0.36/0.56      (((v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56         sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)], ['35', '103'])).
% 0.36/0.56  thf('105', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.56           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf('106', plain,
% 0.36/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.56         ((v2_struct_0 @ X33)
% 0.36/0.56          | ~ (l1_pre_topc @ X33)
% 0.36/0.56          | ((k1_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35)
% 0.36/0.56              != (k2_struct_0 @ X34))
% 0.36/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X35)
% 0.36/0.56              != (k2_struct_0 @ X33))
% 0.36/0.56          | ~ (v2_funct_1 @ X35)
% 0.36/0.56          | ~ (v4_pre_topc @ 
% 0.36/0.56               (k7_relset_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ 
% 0.36/0.56                X35 @ (sk_D_1 @ X35 @ X33 @ X34)) @ 
% 0.36/0.56               X33)
% 0.36/0.56          | ~ (v4_pre_topc @ (sk_D_1 @ X35 @ X33 @ X34) @ X34)
% 0.36/0.56          | (v3_tops_2 @ X35 @ X34 @ X33)
% 0.36/0.56          | ~ (m1_subset_1 @ X35 @ 
% 0.36/0.56               (k1_zfmisc_1 @ 
% 0.36/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.36/0.56          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.36/0.56          | ~ (v1_funct_1 @ X35)
% 0.36/0.56          | ~ (l1_pre_topc @ X34))),
% 0.36/0.56      inference('cnf', [status(esa)], [t72_tops_2])).
% 0.36/0.56  thf('107', plain,
% 0.36/0.56      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56           sk_B)
% 0.36/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.56        | ~ (m1_subset_1 @ sk_C @ 
% 0.36/0.56             (k1_zfmisc_1 @ 
% 0.36/0.56              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.36/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56            != (k2_struct_0 @ sk_B))
% 0.36/0.56        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56            != (k2_struct_0 @ sk_A))
% 0.36/0.56        | ~ (l1_pre_topc @ sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['105', '106'])).
% 0.36/0.56  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('110', plain,
% 0.36/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('111', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C @ 
% 0.36/0.56        (k1_zfmisc_1 @ 
% 0.36/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('112', plain, ((v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.36/0.56      inference('clc', [status(thm)], ['101', '102'])).
% 0.36/0.56  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('114', plain,
% 0.36/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('115', plain,
% 0.36/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.56         = (k2_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('117', plain,
% 0.36/0.56      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56           sk_B)
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.36/0.56        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.36/0.56        | (v2_struct_0 @ sk_B))),
% 0.36/0.56      inference('demod', [status(thm)],
% 0.36/0.56                ['107', '108', '109', '110', '111', '112', '113', '114', 
% 0.36/0.56                 '115', '116'])).
% 0.36/0.56  thf('118', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_B)
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.56        | ~ (v4_pre_topc @ 
% 0.36/0.56             (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ sk_B))),
% 0.36/0.56      inference('simplify', [status(thm)], ['117'])).
% 0.36/0.56  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('120', plain,
% 0.36/0.56      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56           sk_B)
% 0.36/0.56        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.56      inference('clc', [status(thm)], ['118', '119'])).
% 0.36/0.56  thf('121', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('122', plain,
% 0.36/0.56      (~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.56          sk_B)),
% 0.36/0.56      inference('clc', [status(thm)], ['120', '121'])).
% 0.36/0.56  thf('123', plain, ((v2_struct_0 @ sk_B)),
% 0.36/0.56      inference('clc', [status(thm)], ['104', '122'])).
% 0.36/0.56  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
