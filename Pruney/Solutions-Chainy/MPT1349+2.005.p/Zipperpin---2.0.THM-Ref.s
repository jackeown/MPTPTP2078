%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JHmd9HI6bi

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:31 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  450 (264421 expanded)
%              Number of leaves         :   39 (73231 expanded)
%              Depth                    :   41
%              Number of atoms          : 8432 (11311488 expanded)
%              Number of equality atoms :  262 (446089 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t74_tops_2,conjecture,(
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
             => ( ( v3_tops_2 @ C @ A @ B )
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ A @ D ) )
                        = ( k2_pre_topc @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) )).

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
               => ( ( v3_tops_2 @ C @ A @ B )
                <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ A ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ A @ D ) )
                          = ( k2_pre_topc @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tops_2,axiom,(
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
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ A @ D ) ) @ ( k2_pre_topc @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v5_pre_topc @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('2',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k8_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) @ X22 @ X20 )
        = ( k8_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) @ X22 ) @ X20 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) @ X22 )
       != ( k2_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t67_tops_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['18','21','22','23','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ sk_C )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
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
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v3_tops_2 @ X4 @ X5 @ X3 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 )
        = ( k2_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','44'])).

thf('46',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('47',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v3_tops_2 @ X4 @ X5 @ X3 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 )
        = ( k2_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('61',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v3_tops_2 @ X4 @ X5 @ X3 )
      | ( v2_funct_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('74',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('76',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_tops_2,axiom,(
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
               => ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) )).

thf('78',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_tops_2])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('89',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(t73_tops_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
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
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_pre_topc @ B @ D ) )
                        = ( k2_pre_topc @ A @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) )).

thf('94',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v3_tops_2 @ X32 @ X31 @ X30 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 @ ( k2_pre_topc @ X30 @ X33 ) )
        = ( k2_pre_topc @ X31 @ ( k8_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X6 @ X7 @ X8 ) @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','103','109','110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
          = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
          = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','115'])).

thf('117',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('118',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','44'])).

thf('120',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['117','121'])).

thf('123',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('124',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ~ ( v2_funct_1 @ sk_C )
      | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('127',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['18','21','22','23','26'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( v2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ( ( k2_struct_0 @ sk_B )
         != ( k2_struct_0 @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D_2 ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['116','134'])).

thf('136',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('138',plain,
    ( ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['132'])).

thf('142',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_D_2 ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['135','142'])).

thf('144',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
   <= ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('145',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
   <= ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
       != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_D_2 ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_2 ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('149',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('151',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['31','148','150'])).

thf('152',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','103','109','110','111'])).

thf('154',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('155',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('156',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf('157',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X13 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) @ X15 )
       != ( k2_struct_0 @ X13 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) @ X15 ) )
        = ( k2_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('158',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('163',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['158','159','160','161','162'])).

thf('164',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('165',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','167'])).

thf('169',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('170',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 )
       != ( k2_struct_0 @ X31 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 )
       != ( k2_struct_0 @ X30 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ( m1_subset_1 @ ( sk_D_1 @ X32 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_tops_2 @ X32 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('171',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('175',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['171','172','173','174','175','176','177'])).

thf('179',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','178'])).

thf('180',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('181',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('182',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X13 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) @ X15 )
       != ( k2_struct_0 @ X13 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) @ X15 ) )
        = ( k2_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('184',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('189',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['184','185','186','187','188'])).

thf('190',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['181','189'])).

thf('191',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ~ ( v2_funct_1 @ sk_C )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','193'])).

thf('195',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('196',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf('198',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 )
       != ( k2_struct_0 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('199',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('204',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('206',plain,
    ( ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','206'])).

thf('208',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','194','207'])).

thf('209',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('213',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('216',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('219',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('223',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('224',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['221','222','223'])).

thf('225',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('226',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['224','228'])).

thf('230',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 )
       != ( k2_struct_0 @ X31 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 )
       != ( k2_struct_0 @ X30 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 @ ( k2_pre_topc @ X30 @ ( sk_D_1 @ X32 @ X30 @ X31 ) ) )
       != ( k2_pre_topc @ X31 @ ( k8_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 @ ( sk_D_1 @ X32 @ X30 @ X31 ) ) ) )
      | ( v3_tops_2 @ X32 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_2])).

thf('231',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
     != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('235',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('236',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('237',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','206'])).

thf('238',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('240',plain,(
    v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','167'])).

thf('242',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('243',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('244',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','193'])).

thf('246',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('247',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('248',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['245','246','247'])).

thf('249',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
     != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['231','232','233','234','235','236','240','244','248','249','250'])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
     != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
     != ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['216','254'])).

thf('256',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
     != ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('258',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X34 ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X34 ) ) )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X34 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X34 ) ) ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X34 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X34 ) ) ) ) ),
    inference(split,[status(esa)],['258'])).

thf('260',plain,
    ( ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X34 ) )
            = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X34 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['257','259'])).

thf('261',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('262',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('263',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X34 ) )
          = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X34 ) ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['258'])).

thf('264',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ X34 ) )
        = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X34 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','263'])).

thf('265',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['260','261','262','264'])).

thf('266',plain,(
    v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['256','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['153','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['152','269'])).

thf('271',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 )
       != ( k2_struct_0 @ X5 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 )
       != ( k2_struct_0 @ X3 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v5_pre_topc @ X4 @ X5 @ X3 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 ) @ X3 @ X5 )
      | ( v3_tops_2 @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('273',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','44'])).

thf('278',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['273','274','275','276','277','278'])).

thf('280',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('282',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('283',plain,(
    v2_funct_1 @ sk_C ),
    inference(simpl_trail,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['280','283'])).

thf('285',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('286',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('287',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['284','287'])).

thf('289',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('291',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146'])).

thf('292',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['290','291'])).

thf('293',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['289','292'])).

thf('294',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('295',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v3_tops_2 @ X4 @ X5 @ X3 )
      | ( v5_pre_topc @ X4 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('296',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['294','295'])).

thf('297',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('299',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('300',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['296','297','298','299','300'])).

thf('302',plain,(
    v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['256','265'])).

thf('303',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','303'])).

thf('305',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['270','304'])).

thf('306',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('307',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('308',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['308','309'])).

thf('311',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
          = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('312',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','147'])).

thf('314',plain,(
    v2_funct_1 @ sk_C ),
    inference('sat_resolution*',[status(thm)],['33','35','48','62','74','146','149'])).

thf('315',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['312','313','314'])).

thf('316',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['305','315'])).

thf('317',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','303'])).

thf('318',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['151','318'])).

thf('320',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','303'])).

thf('321',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('322',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 @ ( k2_pre_topc @ X11 @ ( sk_D @ X10 @ X9 @ X11 ) ) ) @ ( k2_pre_topc @ X9 @ ( k7_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 @ ( sk_D @ X10 @ X9 @ X11 ) ) ) )
      | ( v5_pre_topc @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('323',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['323','324','325','326','327','328','329','330'])).

thf('332',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','303'])).

thf('333',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['331','332'])).

thf('334',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['333','334'])).

thf('336',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('337',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('338',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('339',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('341',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('342',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['339','340','341'])).

thf('343',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v5_pre_topc @ X10 @ X11 @ X9 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 @ ( k2_pre_topc @ X11 @ X12 ) ) @ ( k2_pre_topc @ X9 @ ( k7_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_tops_2])).

thf('344',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('348',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('349',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['347','348'])).

thf('350',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('351',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('352',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['349','350','351'])).

thf('353',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('354',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X6 @ X7 @ X8 ) @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('355',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['353','354'])).

thf('356',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('357',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('358',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['355','356','357'])).

thf('359',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['344','345','346','352','358','359','360'])).

thf('362',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('363',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v3_tops_2 @ X4 @ X5 @ X3 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X4 ) @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('364',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['362','363'])).

thf('365',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('367',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('368',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['364','365','366','367','368'])).

thf('370',plain,(
    v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['256','265'])).

thf('371',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['369','370'])).

thf('372',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['361','371'])).

thf('373',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('374',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['372','373'])).

thf('375',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['336','374'])).

thf('376',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['308','309'])).

thf('377',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(t68_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf('378',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) @ X26 @ X24 )
        = ( k7_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X25 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) @ X26 ) @ X24 ) )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) @ X26 )
       != ( k2_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t68_tops_2])).

thf('379',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['377','378'])).

thf('380',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('381',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('382',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('383',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('384',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['379','380','381','382','383'])).

thf('385',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['241','242','243'])).

thf('386',plain,(
    v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['237','238','239'])).

thf('387',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['384','385','386'])).

thf('388',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['387'])).

thf('389',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['376','388'])).

thf('390',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['270','304'])).

thf('391',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('392',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['390','391'])).

thf('393',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('394',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['392','393'])).

thf('395',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['389','394'])).

thf('396',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','303'])).

thf('397',plain,
    ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['395','396'])).

thf('398',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('399',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['387'])).

thf('400',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['398','399'])).

thf('401',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','303'])).

thf('402',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    = ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['400','401'])).

thf('403',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('404',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_pre_topc @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['319','320'])).

thf('405',plain,
    ( ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    = ( k2_pre_topc @ sk_B @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['403','404'])).

thf('406',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['375','397','402','405'])).

thf('407',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','303'])).

thf('408',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) @ ( k2_pre_topc @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['406','407'])).

thf('409',plain,(
    $false ),
    inference(demod,[status(thm)],['335','408'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JHmd9HI6bi
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:41:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.99  % Solved by: fo/fo7.sh
% 0.76/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.99  % done 749 iterations in 0.522s
% 0.76/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.99  % SZS output start Refutation
% 0.76/0.99  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.99  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.99  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.76/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.99  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.99  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.76/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.76/0.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.99  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.76/0.99  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.99  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.76/0.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.99  thf(t74_tops_2, conjecture,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99             ( l1_pre_topc @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                 ( m1_subset_1 @
% 0.76/0.99                   C @ 
% 0.76/0.99                   ( k1_zfmisc_1 @
% 0.76/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.76/0.99                 ( ( ( k1_relset_1 @
% 0.76/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                     ( k2_struct_0 @ A ) ) & 
% 0.76/0.99                   ( ( k2_relset_1 @
% 0.76/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                   ( v2_funct_1 @ C ) & 
% 0.76/0.99                   ( ![D:$i]:
% 0.76/0.99                     ( ( m1_subset_1 @
% 0.76/0.99                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99                       ( ( k7_relset_1 @
% 0.76/0.99                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.76/0.99                           ( k2_pre_topc @ A @ D ) ) =
% 0.76/0.99                         ( k2_pre_topc @
% 0.76/0.99                           B @ 
% 0.76/0.99                           ( k7_relset_1 @
% 0.76/0.99                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.99    (~( ![A:$i]:
% 0.76/0.99        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99          ( ![B:$i]:
% 0.76/0.99            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99                ( l1_pre_topc @ B ) ) =>
% 0.76/0.99              ( ![C:$i]:
% 0.76/0.99                ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                    ( v1_funct_2 @
% 0.76/0.99                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                    ( m1_subset_1 @
% 0.76/0.99                      C @ 
% 0.76/0.99                      ( k1_zfmisc_1 @
% 0.76/0.99                        ( k2_zfmisc_1 @
% 0.76/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99                  ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.76/0.99                    ( ( ( k1_relset_1 @
% 0.76/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                        ( k2_struct_0 @ A ) ) & 
% 0.76/0.99                      ( ( k2_relset_1 @
% 0.76/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                      ( v2_funct_1 @ C ) & 
% 0.76/0.99                      ( ![D:$i]:
% 0.76/0.99                        ( ( m1_subset_1 @
% 0.76/0.99                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99                          ( ( k7_relset_1 @
% 0.76/0.99                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.76/0.99                              ( k2_pre_topc @ A @ D ) ) =
% 0.76/0.99                            ( k2_pre_topc @
% 0.76/0.99                              B @ 
% 0.76/0.99                              ( k7_relset_1 @
% 0.76/0.99                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.99                                C @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t74_tops_2])).
% 0.76/0.99  thf('0', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t57_tops_2, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.99             ( l1_pre_topc @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                 ( m1_subset_1 @
% 0.76/0.99                   C @ 
% 0.76/0.99                   ( k1_zfmisc_1 @
% 0.76/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.76/0.99                 ( ![D:$i]:
% 0.76/0.99                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99                     ( r1_tarski @
% 0.76/0.99                       ( k7_relset_1 @
% 0.76/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.76/0.99                         ( k2_pre_topc @ A @ D ) ) @ 
% 0.76/0.99                       ( k2_pre_topc @
% 0.76/0.99                         B @ 
% 0.76/0.99                         ( k7_relset_1 @
% 0.76/0.99                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf('1', plain,
% 0.76/0.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.99         ((v2_struct_0 @ X9)
% 0.76/0.99          | ~ (v2_pre_topc @ X9)
% 0.76/0.99          | ~ (l1_pre_topc @ X9)
% 0.76/0.99          | (m1_subset_1 @ (sk_D @ X10 @ X9 @ X11) @ 
% 0.76/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.76/0.99          | (v5_pre_topc @ X10 @ X11 @ X9)
% 0.76/0.99          | ~ (m1_subset_1 @ X10 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.76/0.99          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.76/0.99          | ~ (v1_funct_1 @ X10)
% 0.76/0.99          | ~ (l1_pre_topc @ X11)
% 0.76/0.99          | ~ (v2_pre_topc @ X11))),
% 0.76/0.99      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.76/0.99  thf('2', plain,
% 0.76/0.99      ((~ (v2_pre_topc @ sk_A)
% 0.76/0.99        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.99        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.99        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.76/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.76/0.99        | ~ (v2_pre_topc @ sk_B)
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.99  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('9', plain,
% 0.76/0.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.99        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.76/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99        | (v2_struct_0 @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['2', '3', '4', '5', '6', '7', '8'])).
% 0.76/0.99  thf('10', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('11', plain,
% 0.76/0.99      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.76/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('clc', [status(thm)], ['9', '10'])).
% 0.76/0.99  thf('12', plain, (((v2_funct_1 @ sk_C) | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('13', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.76/0.99      inference('split', [status(esa)], ['12'])).
% 0.76/0.99  thf('14', plain,
% 0.76/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B))
% 0.76/0.99        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B)))
% 0.76/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.76/0.99      inference('split', [status(esa)], ['14'])).
% 0.76/0.99  thf('16', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t67_tops_2, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_struct_0 @ A ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( l1_struct_0 @ B ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                 ( m1_subset_1 @
% 0.76/0.99                   C @ 
% 0.76/0.99                   ( k1_zfmisc_1 @
% 0.76/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99               ( ![D:$i]:
% 0.76/0.99                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.99                   ( ( ( ( k2_relset_1 @
% 0.76/0.99                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                         ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                       ( v2_funct_1 @ C ) ) =>
% 0.76/0.99                     ( ( k7_relset_1 @
% 0.76/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.76/0.99                       ( k8_relset_1 @
% 0.76/0.99                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.99                         ( k2_tops_2 @
% 0.76/0.99                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.76/0.99                         D ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf('17', plain,
% 0.76/0.99      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.99         (~ (l1_struct_0 @ X19)
% 0.76/0.99          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.76/0.99          | ((k7_relset_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ X22 @ 
% 0.76/0.99              X20)
% 0.76/0.99              = (k8_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21) @ 
% 0.76/0.99                 (k2_tops_2 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ X22) @ 
% 0.76/0.99                 X20))
% 0.76/0.99          | ~ (v2_funct_1 @ X22)
% 0.76/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ X22)
% 0.76/0.99              != (k2_struct_0 @ X19))
% 0.76/0.99          | ~ (m1_subset_1 @ X22 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.76/0.99          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.76/0.99          | ~ (v1_funct_1 @ X22)
% 0.76/0.99          | ~ (l1_struct_0 @ X21))),
% 0.76/0.99      inference('cnf', [status(esa)], [t67_tops_2])).
% 0.76/0.99  thf('18', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (~ (l1_struct_0 @ sk_A)
% 0.76/0.99          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.99          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.99          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99              != (k2_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v2_funct_1 @ sk_C)
% 0.76/0.99          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99              sk_C @ X0)
% 0.76/0.99              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                  sk_C) @ 
% 0.76/0.99                 X0))
% 0.76/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99          | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.99  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(dt_l1_pre_topc, axiom,
% 0.76/0.99    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.76/0.99  thf('20', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.99  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.99  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('23', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('25', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.99  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.99  thf('27', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99            != (k2_struct_0 @ sk_B))
% 0.76/0.99          | ~ (v2_funct_1 @ sk_C)
% 0.76/0.99          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99              sk_C @ X0)
% 0.76/0.99              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                  sk_C) @ 
% 0.76/0.99                 X0))
% 0.76/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.99      inference('demod', [status(thm)], ['18', '21', '22', '23', '26'])).
% 0.76/0.99  thf('28', plain,
% 0.76/0.99      ((![X0 : $i]:
% 0.76/0.99          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.76/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_C @ X0)
% 0.76/0.99               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                   sk_C) @ 
% 0.76/0.99                  X0))
% 0.76/0.99           | ~ (v2_funct_1 @ sk_C)))
% 0.76/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['15', '27'])).
% 0.76/0.99  thf('29', plain,
% 0.76/0.99      ((![X0 : $i]:
% 0.76/0.99          (~ (v2_funct_1 @ sk_C)
% 0.76/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_C @ X0)
% 0.76/0.99               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                   sk_C) @ 
% 0.76/0.99                  X0))
% 0.76/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.76/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.76/0.99      inference('simplify', [status(thm)], ['28'])).
% 0.76/0.99  thf('30', plain,
% 0.76/0.99      ((![X0 : $i]:
% 0.76/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_C @ X0)
% 0.76/0.99               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                   sk_C) @ 
% 0.76/0.99                  X0))))
% 0.76/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.76/0.99             ((v2_funct_1 @ sk_C)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['13', '29'])).
% 0.76/0.99  thf('31', plain,
% 0.76/0.99      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.76/0.99         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.76/0.99             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.76/0.99                (sk_D @ sk_C @ sk_B @ sk_A)))))
% 0.76/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.76/0.99             ((v2_funct_1 @ sk_C)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['11', '30'])).
% 0.76/0.99  thf('32', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99            != (k2_struct_0 @ sk_B))
% 0.76/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99            != (k2_struct_0 @ sk_A))
% 0.76/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('33', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.76/0.99       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.76/0.99       ~
% 0.76/0.99       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_A))) | 
% 0.76/0.99       ~ ((v2_funct_1 @ sk_C)) | 
% 0.76/0.99       ~
% 0.76/0.99       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B)))),
% 0.76/0.99      inference('split', [status(esa)], ['32'])).
% 0.76/0.99  thf('34', plain,
% 0.76/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.76/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.76/0.99          != (k2_pre_topc @ sk_B @ 
% 0.76/0.99              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99               sk_C @ sk_D_2)))
% 0.76/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99            != (k2_struct_0 @ sk_B))
% 0.76/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99            != (k2_struct_0 @ sk_A))
% 0.76/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('35', plain,
% 0.76/0.99      (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.76/0.99       ~
% 0.76/0.99       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.76/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.76/0.99          = (k2_pre_topc @ sk_B @ 
% 0.76/0.99             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99              sk_C @ sk_D_2)))) | 
% 0.76/0.99       ~
% 0.76/0.99       (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_A))) | 
% 0.76/0.99       ~
% 0.76/0.99       (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B))) | 
% 0.76/0.99       ~ ((v2_funct_1 @ sk_C))),
% 0.76/0.99      inference('split', [status(esa)], ['34'])).
% 0.76/0.99  thf('36', plain,
% 0.76/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_A))
% 0.76/0.99        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('37', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(d5_tops_2, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( l1_pre_topc @ A ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( l1_pre_topc @ B ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.99                 ( m1_subset_1 @
% 0.76/0.99                   C @ 
% 0.76/0.99                   ( k1_zfmisc_1 @
% 0.76/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.99               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.76/0.99                 ( ( ( k1_relset_1 @
% 0.76/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                     ( k2_struct_0 @ A ) ) & 
% 0.76/0.99                   ( ( k2_relset_1 @
% 0.76/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.99                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.76/0.99                   ( v5_pre_topc @
% 0.76/0.99                     ( k2_tops_2 @
% 0.76/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.76/0.99                     B @ A ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf('38', plain,
% 0.76/0.99      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ X3)
% 0.76/0.99          | ~ (v3_tops_2 @ X4 @ X5 @ X3)
% 0.76/0.99          | ((k1_relset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4)
% 0.76/0.99              = (k2_struct_0 @ X5))
% 0.76/0.99          | ~ (m1_subset_1 @ X4 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.76/0.99          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.76/0.99          | ~ (v1_funct_1 @ X4)
% 0.76/0.99          | ~ (l1_pre_topc @ X5))),
% 0.76/0.99      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.76/0.99  thf('39', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99            = (k2_struct_0 @ sk_A))
% 0.76/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.99        | ~ (l1_pre_topc @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['37', '38'])).
% 0.76/0.99  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('42', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('44', plain,
% 0.76/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_A))
% 0.76/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99         = (k2_struct_0 @ sk_A))),
% 0.76/0.99      inference('clc', [status(thm)], ['36', '44'])).
% 0.76/0.99  thf('46', plain,
% 0.76/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('split', [status(esa)], ['34'])).
% 0.76/0.99  thf('47', plain,
% 0.76/0.99      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_A))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.99  thf('48', plain,
% 0.76/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_A)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['47'])).
% 0.76/0.99  thf('49', plain,
% 0.76/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_A))
% 0.76/0.99        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('50', plain,
% 0.76/0.99      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.76/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.99      inference('split', [status(esa)], ['49'])).
% 0.76/0.99  thf('51', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.76/0.99        (k1_zfmisc_1 @ 
% 0.76/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('52', plain,
% 0.76/0.99      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.99         (~ (l1_pre_topc @ X3)
% 0.76/0.99          | ~ (v3_tops_2 @ X4 @ X5 @ X3)
% 0.76/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4)
% 0.76/0.99              = (k2_struct_0 @ X3))
% 0.76/0.99          | ~ (m1_subset_1 @ X4 @ 
% 0.76/0.99               (k1_zfmisc_1 @ 
% 0.76/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.76/0.99          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.76/0.99          | ~ (v1_funct_1 @ X4)
% 0.76/0.99          | ~ (l1_pre_topc @ X5))),
% 0.76/0.99      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99            = (k2_struct_0 @ sk_B))
% 0.76/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.76/0.99        | ~ (l1_pre_topc @ sk_B))),
% 0.76/0.99      inference('sup-', [status(thm)], ['51', '52'])).
% 0.76/0.99  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('56', plain,
% 0.76/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('58', plain,
% 0.76/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B))
% 0.76/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.76/0.99  thf('59', plain,
% 0.76/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B)))
% 0.76/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['50', '58'])).
% 0.76/0.99  thf('60', plain,
% 0.76/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          != (k2_struct_0 @ sk_B)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.76/0.99      inference('split', [status(esa)], ['34'])).
% 0.76/0.99  thf('61', plain,
% 0.76/0.99      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.76/0.99         <= (~
% 0.76/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.76/0.99             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.99  thf('62', plain,
% 0.76/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.99          = (k2_struct_0 @ sk_B))) | 
% 0.76/0.99       ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.76/0.99      inference('simplify', [status(thm)], ['61'])).
% 0.76/0.99  thf('63', plain,
% 0.76/0.99      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.76/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.76/0.99      inference('split', [status(esa)], ['49'])).
% 0.76/0.99  thf('64', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('65', plain,
% 0.83/0.99      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.83/0.99         (~ (l1_pre_topc @ X3)
% 0.83/0.99          | ~ (v3_tops_2 @ X4 @ X5 @ X3)
% 0.83/0.99          | (v2_funct_1 @ X4)
% 0.83/0.99          | ~ (m1_subset_1 @ X4 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.83/0.99          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.83/0.99          | ~ (v1_funct_1 @ X4)
% 0.83/0.99          | ~ (l1_pre_topc @ X5))),
% 0.83/0.99      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.83/0.99  thf('66', plain,
% 0.83/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.83/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | (v2_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | ~ (l1_pre_topc @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['64', '65'])).
% 0.83/0.99  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('69', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('71', plain,
% 0.83/0.99      (((v2_funct_1 @ sk_C) | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.83/0.99  thf('72', plain,
% 0.83/0.99      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['63', '71'])).
% 0.83/0.99  thf('73', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('split', [status(esa)], ['34'])).
% 0.83/0.99  thf('74', plain,
% 0.83/0.99      (((v2_funct_1 @ sk_C)) | ~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['72', '73'])).
% 0.83/0.99  thf('75', plain,
% 0.83/0.99      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.83/0.99         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.83/0.99      inference('split', [status(esa)], ['32'])).
% 0.83/0.99  thf('76', plain,
% 0.83/0.99      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('split', [status(esa)], ['49'])).
% 0.83/0.99  thf('77', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf(t70_tops_2, axiom,
% 0.83/0.99    (![A:$i]:
% 0.83/0.99     ( ( l1_pre_topc @ A ) =>
% 0.83/0.99       ( ![B:$i]:
% 0.83/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.83/0.99           ( ![C:$i]:
% 0.83/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.83/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/0.99                 ( m1_subset_1 @
% 0.83/0.99                   C @ 
% 0.83/0.99                   ( k1_zfmisc_1 @
% 0.83/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/0.99               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.83/0.99                 ( v3_tops_2 @
% 0.83/0.99                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.83/0.99                   B @ A ) ) ) ) ) ) ))).
% 0.83/0.99  thf('78', plain,
% 0.83/0.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.83/0.99         ((v2_struct_0 @ X27)
% 0.83/0.99          | ~ (l1_pre_topc @ X27)
% 0.83/0.99          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 0.83/0.99          | (v3_tops_2 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28) @ 
% 0.83/0.99             X27 @ X29)
% 0.83/0.99          | ~ (m1_subset_1 @ X28 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 0.83/0.99          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 0.83/0.99          | ~ (v1_funct_1 @ X28)
% 0.83/0.99          | ~ (l1_pre_topc @ X29))),
% 0.83/0.99      inference('cnf', [status(esa)], [t70_tops_2])).
% 0.83/0.99  thf('79', plain,
% 0.83/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.83/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.83/0.99        | (v2_struct_0 @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['77', '78'])).
% 0.83/0.99  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('82', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('84', plain,
% 0.83/0.99      (((v3_tops_2 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99         sk_B @ sk_A)
% 0.83/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | (v2_struct_0 @ sk_B))),
% 0.83/0.99      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.83/0.99  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('86', plain,
% 0.83/0.99      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A))),
% 0.83/0.99      inference('clc', [status(thm)], ['84', '85'])).
% 0.83/0.99  thf('87', plain,
% 0.83/0.99      (((v3_tops_2 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99         sk_B @ sk_A)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['76', '86'])).
% 0.83/0.99  thf('88', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf(dt_k2_tops_2, axiom,
% 0.83/0.99    (![A:$i,B:$i,C:$i]:
% 0.83/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/0.99       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.83/0.99         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.83/0.99         ( m1_subset_1 @
% 0.83/0.99           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.83/0.99           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.83/0.99  thf('89', plain,
% 0.83/0.99      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/0.99         ((m1_subset_1 @ (k2_tops_2 @ X6 @ X7 @ X8) @ 
% 0.83/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.83/0.99          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.83/0.99          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.83/0.99          | ~ (v1_funct_1 @ X8))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.83/0.99  thf('90', plain,
% 0.83/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | (m1_subset_1 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           (k1_zfmisc_1 @ 
% 0.83/0.99            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['88', '89'])).
% 0.83/0.99  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('92', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('93', plain,
% 0.83/0.99      ((m1_subset_1 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/0.99      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/0.99  thf(t73_tops_2, axiom,
% 0.83/0.99    (![A:$i]:
% 0.83/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/0.99       ( ![B:$i]:
% 0.83/0.99         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.83/0.99           ( ![C:$i]:
% 0.83/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.83/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/0.99                 ( m1_subset_1 @
% 0.83/0.99                   C @ 
% 0.83/0.99                   ( k1_zfmisc_1 @
% 0.83/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/0.99               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.83/0.99                 ( ( ( k1_relset_1 @
% 0.83/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/0.99                     ( k2_struct_0 @ A ) ) & 
% 0.83/0.99                   ( ( k2_relset_1 @
% 0.83/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.83/0.99                   ( v2_funct_1 @ C ) & 
% 0.83/0.99                   ( ![D:$i]:
% 0.83/0.99                     ( ( m1_subset_1 @
% 0.83/0.99                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.83/0.99                       ( ( k8_relset_1 @
% 0.83/0.99                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.83/0.99                           ( k2_pre_topc @ B @ D ) ) =
% 0.83/0.99                         ( k2_pre_topc @
% 0.83/0.99                           A @ 
% 0.83/0.99                           ( k8_relset_1 @
% 0.83/0.99                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.83/0.99  thf('94', plain,
% 0.83/0.99      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.83/0.99         (~ (v2_pre_topc @ X30)
% 0.83/0.99          | ~ (l1_pre_topc @ X30)
% 0.83/0.99          | ~ (v3_tops_2 @ X32 @ X31 @ X30)
% 0.83/0.99          | ((k8_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32 @ 
% 0.83/0.99              (k2_pre_topc @ X30 @ X33))
% 0.83/0.99              = (k2_pre_topc @ X31 @ 
% 0.83/0.99                 (k8_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ 
% 0.83/0.99                  X32 @ X33)))
% 0.83/0.99          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.83/0.99          | ~ (m1_subset_1 @ X32 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 0.83/0.99          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.83/0.99          | ~ (v1_funct_1 @ X32)
% 0.83/0.99          | ~ (l1_pre_topc @ X31)
% 0.83/0.99          | ~ (v2_pre_topc @ X31)
% 0.83/0.99          | (v2_struct_0 @ X31))),
% 0.83/0.99      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.83/0.99  thf('95', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         ((v2_struct_0 @ sk_B)
% 0.83/0.99          | ~ (v2_pre_topc @ sk_B)
% 0.83/0.99          | ~ (l1_pre_topc @ sk_B)
% 0.83/0.99          | ~ (v1_funct_1 @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99          | ~ (v1_funct_2 @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              (k2_pre_topc @ sk_A @ X0))
% 0.83/0.99              = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0)))
% 0.83/0.99          | ~ (v3_tops_2 @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               sk_B @ sk_A)
% 0.83/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.83/0.99          | ~ (v2_pre_topc @ sk_A))),
% 0.83/0.99      inference('sup-', [status(thm)], ['93', '94'])).
% 0.83/0.99  thf('96', plain, ((v2_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('98', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('99', plain,
% 0.83/0.99      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/0.99         ((v1_funct_1 @ (k2_tops_2 @ X6 @ X7 @ X8))
% 0.83/0.99          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.83/0.99          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.83/0.99          | ~ (v1_funct_1 @ X8))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.83/0.99  thf('100', plain,
% 0.83/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | (v1_funct_1 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['98', '99'])).
% 0.83/0.99  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('102', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('103', plain,
% 0.83/0.99      ((v1_funct_1 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/0.99      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/0.99  thf('104', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('105', plain,
% 0.83/0.99      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/0.99         ((v1_funct_2 @ (k2_tops_2 @ X6 @ X7 @ X8) @ X7 @ X6)
% 0.83/0.99          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.83/0.99          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.83/0.99          | ~ (v1_funct_1 @ X8))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.83/0.99  thf('106', plain,
% 0.83/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | (v1_funct_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['104', '105'])).
% 0.83/0.99  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('108', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('109', plain,
% 0.83/0.99      ((v1_funct_2 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/0.99      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/0.99  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('112', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         ((v2_struct_0 @ sk_B)
% 0.83/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              (k2_pre_topc @ sk_A @ X0))
% 0.83/0.99              = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0)))
% 0.83/0.99          | ~ (v3_tops_2 @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               sk_B @ sk_A))),
% 0.83/0.99      inference('demod', [status(thm)],
% 0.83/0.99                ['95', '96', '97', '103', '109', '110', '111'])).
% 0.83/0.99  thf('113', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             (k2_pre_topc @ sk_A @ X0))
% 0.83/0.99             = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C) @ 
% 0.83/0.99                 X0)))
% 0.83/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | (v2_struct_0 @ sk_B)))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['87', '112'])).
% 0.83/0.99  thf('114', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('115', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (k2_pre_topc @ sk_A @ X0))
% 0.83/0.99               = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                  (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                   (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                    sk_C) @ 
% 0.83/0.99                   X0)))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('clc', [status(thm)], ['113', '114'])).
% 0.83/0.99  thf('116', plain,
% 0.83/0.99      ((((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99          = (k2_pre_topc @ sk_B @ 
% 0.83/0.99             (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_D_2))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.83/0.99             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['75', '115'])).
% 0.83/0.99  thf('117', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['50', '58'])).
% 0.83/0.99  thf('118', plain,
% 0.83/0.99      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_A))
% 0.83/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('119', plain,
% 0.83/0.99      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99         = (k2_struct_0 @ sk_A))),
% 0.83/0.99      inference('clc', [status(thm)], ['36', '44'])).
% 0.83/0.99  thf('120', plain,
% 0.83/0.99      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.83/0.99        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('demod', [status(thm)], ['118', '119'])).
% 0.83/0.99  thf('121', plain,
% 0.83/0.99      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/0.99      inference('simplify', [status(thm)], ['120'])).
% 0.83/0.99  thf('122', plain,
% 0.83/0.99      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99         | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['117', '121'])).
% 0.83/0.99  thf('123', plain,
% 0.83/0.99      (((v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('split', [status(esa)], ['49'])).
% 0.83/0.99  thf('124', plain,
% 0.83/0.99      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99         | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C))) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)], ['122', '123'])).
% 0.83/0.99  thf('125', plain,
% 0.83/0.99      (((~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('simplify', [status(thm)], ['124'])).
% 0.83/0.99  thf('126', plain,
% 0.83/0.99      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['63', '71'])).
% 0.83/0.99  thf('127', plain,
% 0.83/0.99      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)], ['125', '126'])).
% 0.83/0.99  thf('128', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['50', '58'])).
% 0.83/0.99  thf('129', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99          | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99              sk_C @ X0)
% 0.83/0.99              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C) @ 
% 0.83/0.99                 X0))
% 0.83/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/0.99      inference('demod', [status(thm)], ['18', '21', '22', '23', '26'])).
% 0.83/0.99  thf('130', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ X0)
% 0.83/0.99               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0))
% 0.83/0.99           | ~ (v2_funct_1 @ sk_C)))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['128', '129'])).
% 0.83/0.99  thf('131', plain,
% 0.83/0.99      (((v2_funct_1 @ sk_C)) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['63', '71'])).
% 0.83/0.99  thf('132', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ X0)
% 0.83/0.99               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)], ['130', '131'])).
% 0.83/0.99  thf('133', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99             sk_C @ X0)
% 0.83/0.99             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                X0))
% 0.83/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('simplify', [status(thm)], ['132'])).
% 0.83/0.99  thf('134', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          sk_D_2)
% 0.83/0.99          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             sk_D_2)))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['127', '133'])).
% 0.83/0.99  thf('135', plain,
% 0.83/0.99      ((((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99          = (k2_pre_topc @ sk_B @ 
% 0.83/0.99             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99              sk_C @ sk_D_2))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.83/0.99             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.83/0.99      inference('demod', [status(thm)], ['116', '134'])).
% 0.83/0.99  thf('136', plain,
% 0.83/0.99      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)], ['125', '126'])).
% 0.83/0.99  thf(dt_k2_pre_topc, axiom,
% 0.83/0.99    (![A:$i,B:$i]:
% 0.83/0.99     ( ( ( l1_pre_topc @ A ) & 
% 0.83/0.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.83/0.99       ( m1_subset_1 @
% 0.83/0.99         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/0.99  thf('137', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (~ (l1_pre_topc @ X0)
% 0.83/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.83/0.99          | (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 0.83/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.83/0.99  thf('138', plain,
% 0.83/0.99      ((((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_2) @ 
% 0.83/0.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | ~ (l1_pre_topc @ sk_A))) <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['136', '137'])).
% 0.83/0.99  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('140', plain,
% 0.83/0.99      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_D_2) @ 
% 0.83/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)], ['138', '139'])).
% 0.83/0.99  thf('141', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99             sk_C @ X0)
% 0.83/0.99             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                X0))
% 0.83/0.99           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('simplify', [status(thm)], ['132'])).
% 0.83/0.99  thf('142', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99          = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             (k2_pre_topc @ sk_A @ sk_D_2))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['140', '141'])).
% 0.83/0.99  thf('143', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99          = (k2_pre_topc @ sk_B @ 
% 0.83/0.99             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99              sk_C @ sk_D_2))))
% 0.83/0.99         <= (((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.83/0.99             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.83/0.99      inference('sup+', [status(thm)], ['135', '142'])).
% 0.83/0.99  thf('144', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99          != (k2_pre_topc @ sk_B @ 
% 0.83/0.99              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ sk_D_2))))
% 0.83/0.99         <= (~
% 0.83/0.99             (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99                = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                   (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                    (u1_struct_0 @ sk_B) @ sk_C @ sk_D_2)))))),
% 0.83/0.99      inference('split', [status(esa)], ['34'])).
% 0.83/0.99  thf('145', plain,
% 0.83/0.99      ((((k2_pre_topc @ sk_B @ 
% 0.83/0.99          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99           sk_D_2))
% 0.83/0.99          != (k2_pre_topc @ sk_B @ 
% 0.83/0.99              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ sk_D_2))))
% 0.83/0.99         <= (~
% 0.83/0.99             (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C @ (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99                = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                   (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                    (u1_struct_0 @ sk_B) @ sk_C @ sk_D_2)))) & 
% 0.83/0.99             ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.83/0.99             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['143', '144'])).
% 0.83/0.99  thf('146', plain,
% 0.83/0.99      (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.83/0.99       ~ ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.83/0.99       (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ sk_D_2))
% 0.83/0.99          = (k2_pre_topc @ sk_B @ 
% 0.83/0.99             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99              sk_C @ sk_D_2))))),
% 0.83/0.99      inference('simplify', [status(thm)], ['145'])).
% 0.83/0.99  thf('147', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B))) | 
% 0.83/0.99       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('split', [status(esa)], ['14'])).
% 0.83/0.99  thf('148', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('149', plain,
% 0.83/0.99      (((v2_funct_1 @ sk_C)) | ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('split', [status(esa)], ['12'])).
% 0.83/0.99  thf('150', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('151', plain,
% 0.83/0.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.83/0.99            = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['31', '148', '150'])).
% 0.83/0.99  thf('152', plain,
% 0.83/0.99      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.83/0.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('clc', [status(thm)], ['9', '10'])).
% 0.83/0.99  thf('153', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         ((v2_struct_0 @ sk_B)
% 0.83/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              (k2_pre_topc @ sk_A @ X0))
% 0.83/0.99              = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0)))
% 0.83/0.99          | ~ (v3_tops_2 @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               sk_B @ sk_A))),
% 0.83/0.99      inference('demod', [status(thm)],
% 0.83/0.99                ['95', '96', '97', '103', '109', '110', '111'])).
% 0.83/0.99  thf('154', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('split', [status(esa)], ['12'])).
% 0.83/0.99  thf('155', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('split', [status(esa)], ['14'])).
% 0.83/0.99  thf('156', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf(t62_tops_2, axiom,
% 0.83/0.99    (![A:$i]:
% 0.83/0.99     ( ( l1_struct_0 @ A ) =>
% 0.83/0.99       ( ![B:$i]:
% 0.83/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.83/0.99           ( ![C:$i]:
% 0.83/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.83/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/0.99                 ( m1_subset_1 @
% 0.83/0.99                   C @ 
% 0.83/0.99                   ( k1_zfmisc_1 @
% 0.83/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/0.99               ( ( ( ( k2_relset_1 @
% 0.83/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.83/0.99                   ( v2_funct_1 @ C ) ) =>
% 0.83/0.99                 ( ( ( k1_relset_1 @
% 0.83/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/0.99                       ( k2_tops_2 @
% 0.83/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.83/0.99                   ( ( k2_relset_1 @
% 0.83/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/0.99                       ( k2_tops_2 @
% 0.83/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/0.99                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.83/0.99  thf('157', plain,
% 0.83/0.99      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/0.99         ((v2_struct_0 @ X13)
% 0.83/0.99          | ~ (l1_struct_0 @ X13)
% 0.83/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13) @ X15)
% 0.83/0.99              != (k2_struct_0 @ X13))
% 0.83/0.99          | ~ (v2_funct_1 @ X15)
% 0.83/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13) @ X15))
% 0.83/0.99              = (k2_struct_0 @ X14))
% 0.83/0.99          | ~ (m1_subset_1 @ X15 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13))))
% 0.83/0.99          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13))
% 0.83/0.99          | ~ (v1_funct_1 @ X15)
% 0.83/0.99          | ~ (l1_struct_0 @ X14))),
% 0.83/0.99      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.83/0.99  thf('158', plain,
% 0.83/0.99      ((~ (l1_struct_0 @ sk_A)
% 0.83/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            = (k2_struct_0 @ sk_A))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (l1_struct_0 @ sk_B)
% 0.83/0.99        | (v2_struct_0 @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['156', '157'])).
% 0.83/0.99  thf('159', plain, ((l1_struct_0 @ sk_A)),
% 0.83/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.83/0.99  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('161', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('162', plain, ((l1_struct_0 @ sk_B)),
% 0.83/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.83/0.99  thf('163', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99          = (k2_struct_0 @ sk_A))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | (v2_struct_0 @ sk_B))),
% 0.83/0.99      inference('demod', [status(thm)], ['158', '159', '160', '161', '162'])).
% 0.83/0.99  thf('164', plain,
% 0.83/0.99      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99         | (v2_struct_0 @ sk_B)
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99             = (k2_struct_0 @ sk_A))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['155', '163'])).
% 0.83/0.99  thf('165', plain,
% 0.83/0.99      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99           = (k2_struct_0 @ sk_A))
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | (v2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('simplify', [status(thm)], ['164'])).
% 0.83/0.99  thf('166', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('167', plain,
% 0.83/0.99      (((~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99             = (k2_struct_0 @ sk_A))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('clc', [status(thm)], ['165', '166'])).
% 0.83/0.99  thf('168', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99          = (k2_struct_0 @ sk_A)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['154', '167'])).
% 0.83/0.99  thf('169', plain,
% 0.83/0.99      ((m1_subset_1 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/0.99      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/0.99  thf('170', plain,
% 0.83/0.99      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.83/0.99         (~ (v2_pre_topc @ X30)
% 0.83/0.99          | ~ (l1_pre_topc @ X30)
% 0.83/0.99          | ((k1_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32)
% 0.83/0.99              != (k2_struct_0 @ X31))
% 0.83/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32)
% 0.83/0.99              != (k2_struct_0 @ X30))
% 0.83/0.99          | ~ (v2_funct_1 @ X32)
% 0.83/0.99          | (m1_subset_1 @ (sk_D_1 @ X32 @ X30 @ X31) @ 
% 0.83/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.83/0.99          | (v3_tops_2 @ X32 @ X31 @ X30)
% 0.83/0.99          | ~ (m1_subset_1 @ X32 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 0.83/0.99          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.83/0.99          | ~ (v1_funct_1 @ X32)
% 0.83/0.99          | ~ (l1_pre_topc @ X31)
% 0.83/0.99          | ~ (v2_pre_topc @ X31)
% 0.83/0.99          | (v2_struct_0 @ X31))),
% 0.83/0.99      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.83/0.99  thf('171', plain,
% 0.83/0.99      (((v2_struct_0 @ sk_B)
% 0.83/0.99        | ~ (v2_pre_topc @ sk_B)
% 0.83/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.83/0.99        | ~ (v1_funct_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99        | ~ (v1_funct_2 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | (m1_subset_1 @ 
% 0.83/0.99           (sk_D_1 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_A @ sk_B) @ 
% 0.83/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99        | ~ (v2_funct_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            != (k2_struct_0 @ sk_A))
% 0.83/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (l1_pre_topc @ sk_A)
% 0.83/0.99        | ~ (v2_pre_topc @ sk_A))),
% 0.83/0.99      inference('sup-', [status(thm)], ['169', '170'])).
% 0.83/0.99  thf('172', plain, ((v2_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('173', plain, ((l1_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('174', plain,
% 0.83/0.99      ((v1_funct_1 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/0.99      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/0.99  thf('175', plain,
% 0.83/0.99      ((v1_funct_2 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/0.99      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/0.99  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('178', plain,
% 0.83/0.99      (((v2_struct_0 @ sk_B)
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | (m1_subset_1 @ 
% 0.83/0.99           (sk_D_1 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_A @ sk_B) @ 
% 0.83/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99        | ~ (v2_funct_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            != (k2_struct_0 @ sk_A))
% 0.83/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            != (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)],
% 0.83/0.99                ['171', '172', '173', '174', '175', '176', '177'])).
% 0.83/0.99  thf('179', plain,
% 0.83/0.99      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.83/0.99         | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99             != (k2_struct_0 @ sk_B))
% 0.83/0.99         | ~ (v2_funct_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99         | (m1_subset_1 @ 
% 0.83/0.99            (sk_D_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             sk_A @ sk_B) @ 
% 0.83/0.99            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | (v3_tops_2 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_B @ sk_A)
% 0.83/0.99         | (v2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['168', '178'])).
% 0.83/0.99  thf('180', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('split', [status(esa)], ['12'])).
% 0.83/0.99  thf('181', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('split', [status(esa)], ['14'])).
% 0.83/0.99  thf('182', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('183', plain,
% 0.83/0.99      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/0.99         ((v2_struct_0 @ X13)
% 0.83/0.99          | ~ (l1_struct_0 @ X13)
% 0.83/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13) @ X15)
% 0.83/0.99              != (k2_struct_0 @ X13))
% 0.83/0.99          | ~ (v2_funct_1 @ X15)
% 0.83/0.99          | ((k1_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13) @ X15))
% 0.83/0.99              = (k2_struct_0 @ X13))
% 0.83/0.99          | ~ (m1_subset_1 @ X15 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13))))
% 0.83/0.99          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13))
% 0.83/0.99          | ~ (v1_funct_1 @ X15)
% 0.83/0.99          | ~ (l1_struct_0 @ X14))),
% 0.83/0.99      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.83/0.99  thf('184', plain,
% 0.83/0.99      ((~ (l1_struct_0 @ sk_A)
% 0.83/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            = (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (l1_struct_0 @ sk_B)
% 0.83/0.99        | (v2_struct_0 @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['182', '183'])).
% 0.83/0.99  thf('185', plain, ((l1_struct_0 @ sk_A)),
% 0.83/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.83/0.99  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('187', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('188', plain, ((l1_struct_0 @ sk_B)),
% 0.83/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.83/0.99  thf('189', plain,
% 0.83/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99          = (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | (v2_struct_0 @ sk_B))),
% 0.83/0.99      inference('demod', [status(thm)], ['184', '185', '186', '187', '188'])).
% 0.83/0.99  thf('190', plain,
% 0.83/0.99      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99         | (v2_struct_0 @ sk_B)
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99             = (k2_struct_0 @ sk_B))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['181', '189'])).
% 0.83/0.99  thf('191', plain,
% 0.83/0.99      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99           = (k2_struct_0 @ sk_B))
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | (v2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('simplify', [status(thm)], ['190'])).
% 0.83/0.99  thf('192', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('193', plain,
% 0.83/0.99      (((~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99             = (k2_struct_0 @ sk_B))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('clc', [status(thm)], ['191', '192'])).
% 0.83/0.99  thf('194', plain,
% 0.83/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99          = (k2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['180', '193'])).
% 0.83/0.99  thf('195', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('split', [status(esa)], ['12'])).
% 0.83/0.99  thf('196', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('split', [status(esa)], ['14'])).
% 0.83/0.99  thf('197', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf(t63_tops_2, axiom,
% 0.83/0.99    (![A:$i]:
% 0.83/0.99     ( ( l1_struct_0 @ A ) =>
% 0.83/0.99       ( ![B:$i]:
% 0.83/0.99         ( ( l1_struct_0 @ B ) =>
% 0.83/0.99           ( ![C:$i]:
% 0.83/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.83/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/0.99                 ( m1_subset_1 @
% 0.83/0.99                   C @ 
% 0.83/0.99                   ( k1_zfmisc_1 @
% 0.83/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/0.99               ( ( ( ( k2_relset_1 @
% 0.83/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.83/0.99                   ( v2_funct_1 @ C ) ) =>
% 0.83/0.99                 ( v2_funct_1 @
% 0.83/0.99                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.83/0.99  thf('198', plain,
% 0.83/0.99      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.83/0.99         (~ (l1_struct_0 @ X16)
% 0.83/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.83/0.99              != (k2_struct_0 @ X16))
% 0.83/0.99          | ~ (v2_funct_1 @ X18)
% 0.83/0.99          | (v2_funct_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.83/0.99          | ~ (m1_subset_1 @ X18 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.83/0.99          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.83/0.99          | ~ (v1_funct_1 @ X18)
% 0.83/0.99          | ~ (l1_struct_0 @ X17))),
% 0.83/0.99      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.83/0.99  thf('199', plain,
% 0.83/0.99      ((~ (l1_struct_0 @ sk_A)
% 0.83/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | (v2_funct_1 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['197', '198'])).
% 0.83/0.99  thf('200', plain, ((l1_struct_0 @ sk_A)),
% 0.83/0.99      inference('sup-', [status(thm)], ['19', '20'])).
% 0.83/0.99  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('202', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('203', plain, ((l1_struct_0 @ sk_B)),
% 0.83/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.83/0.99  thf('204', plain,
% 0.83/0.99      (((v2_funct_1 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 0.83/0.99  thf('205', plain,
% 0.83/0.99      (((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99         | (v2_funct_1 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['196', '204'])).
% 0.83/0.99  thf('206', plain,
% 0.83/0.99      ((((v2_funct_1 @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99         | ~ (v2_funct_1 @ sk_C)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/0.99      inference('simplify', [status(thm)], ['205'])).
% 0.83/0.99  thf('207', plain,
% 0.83/0.99      (((v2_funct_1 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['195', '206'])).
% 0.83/0.99  thf('208', plain,
% 0.83/0.99      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.83/0.99         | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/0.99         | (m1_subset_1 @ 
% 0.83/0.99            (sk_D_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             sk_A @ sk_B) @ 
% 0.83/0.99            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | (v3_tops_2 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_B @ sk_A)
% 0.83/0.99         | (v2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('demod', [status(thm)], ['179', '194', '207'])).
% 0.83/0.99  thf('209', plain,
% 0.83/0.99      ((((v2_struct_0 @ sk_B)
% 0.83/0.99         | (v3_tops_2 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_B @ sk_A)
% 0.83/0.99         | (m1_subset_1 @ 
% 0.83/0.99            (sk_D_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             sk_A @ sk_B) @ 
% 0.83/0.99            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('simplify', [status(thm)], ['208'])).
% 0.83/0.99  thf('210', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('211', plain,
% 0.83/0.99      ((((m1_subset_1 @ 
% 0.83/0.99          (sk_D_1 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_A @ sk_B) @ 
% 0.83/0.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | (v3_tops_2 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_B @ sk_A)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('clc', [status(thm)], ['209', '210'])).
% 0.83/0.99  thf('212', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ X0)
% 0.83/0.99               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['13', '29'])).
% 0.83/0.99  thf('213', plain,
% 0.83/0.99      ((((v3_tops_2 @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99          sk_B @ sk_A)
% 0.83/0.99         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99             sk_C @ 
% 0.83/0.99             (sk_D_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_A @ sk_B))
% 0.83/0.99             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                (sk_D_1 @ 
% 0.83/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C) @ 
% 0.83/0.99                 sk_A @ sk_B)))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['211', '212'])).
% 0.83/0.99  thf('214', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('215', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('216', plain,
% 0.83/0.99      (((v3_tops_2 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99         sk_B @ sk_A)
% 0.83/0.99        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99            (sk_D_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             sk_A @ sk_B))
% 0.83/0.99            = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (sk_D_1 @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                sk_A @ sk_B))))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['213', '214', '215'])).
% 0.83/0.99  thf('217', plain,
% 0.83/0.99      ((((m1_subset_1 @ 
% 0.83/0.99          (sk_D_1 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_A @ sk_B) @ 
% 0.83/0.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | (v3_tops_2 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_B @ sk_A)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('clc', [status(thm)], ['209', '210'])).
% 0.83/0.99  thf('218', plain,
% 0.83/0.99      (![X0 : $i, X1 : $i]:
% 0.83/0.99         (~ (l1_pre_topc @ X0)
% 0.83/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.83/0.99          | (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 0.83/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.83/0.99      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.83/0.99  thf('219', plain,
% 0.83/0.99      ((((v3_tops_2 @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99          sk_B @ sk_A)
% 0.83/0.99         | (m1_subset_1 @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ 
% 0.83/0.99             (sk_D_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_A @ sk_B)) @ 
% 0.83/0.99            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | ~ (l1_pre_topc @ sk_A)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['217', '218'])).
% 0.83/0.99  thf('220', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('221', plain,
% 0.83/0.99      ((((v3_tops_2 @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99          sk_B @ sk_A)
% 0.83/0.99         | (m1_subset_1 @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ 
% 0.83/0.99             (sk_D_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_A @ sk_B)) @ 
% 0.83/0.99            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('demod', [status(thm)], ['219', '220'])).
% 0.83/0.99  thf('222', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('223', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('224', plain,
% 0.83/0.99      (((v3_tops_2 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99         sk_B @ sk_A)
% 0.83/0.99        | (m1_subset_1 @ 
% 0.83/0.99           (k2_pre_topc @ sk_A @ 
% 0.83/0.99            (sk_D_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             sk_A @ sk_B)) @ 
% 0.83/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['221', '222', '223'])).
% 0.83/0.99  thf('225', plain,
% 0.83/0.99      ((![X0 : $i]:
% 0.83/0.99          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ X0)
% 0.83/0.99               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['13', '29'])).
% 0.83/0.99  thf('226', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('227', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('228', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99              sk_C @ X0)
% 0.83/0.99              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C) @ 
% 0.83/0.99                 X0)))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['225', '226', '227'])).
% 0.83/0.99  thf('229', plain,
% 0.83/0.99      (((v3_tops_2 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99         sk_B @ sk_A)
% 0.83/0.99        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ 
% 0.83/0.99             (sk_D_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_A @ sk_B)))
% 0.83/0.99            = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (k2_pre_topc @ sk_A @ 
% 0.83/0.99                (sk_D_1 @ 
% 0.83/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C) @ 
% 0.83/0.99                 sk_A @ sk_B)))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['224', '228'])).
% 0.83/0.99  thf('230', plain,
% 0.83/0.99      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.83/0.99         (~ (v2_pre_topc @ X30)
% 0.83/0.99          | ~ (l1_pre_topc @ X30)
% 0.83/0.99          | ((k1_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32)
% 0.83/0.99              != (k2_struct_0 @ X31))
% 0.83/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32)
% 0.83/0.99              != (k2_struct_0 @ X30))
% 0.83/0.99          | ~ (v2_funct_1 @ X32)
% 0.83/0.99          | ((k8_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32 @ 
% 0.83/0.99              (k2_pre_topc @ X30 @ (sk_D_1 @ X32 @ X30 @ X31)))
% 0.83/0.99              != (k2_pre_topc @ X31 @ 
% 0.83/0.99                  (k8_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ 
% 0.83/0.99                   X32 @ (sk_D_1 @ X32 @ X30 @ X31))))
% 0.83/0.99          | (v3_tops_2 @ X32 @ X31 @ X30)
% 0.83/0.99          | ~ (m1_subset_1 @ X32 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 0.83/0.99          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.83/0.99          | ~ (v1_funct_1 @ X32)
% 0.83/0.99          | ~ (l1_pre_topc @ X31)
% 0.83/0.99          | ~ (v2_pre_topc @ X31)
% 0.83/0.99          | (v2_struct_0 @ X31))),
% 0.83/0.99      inference('cnf', [status(esa)], [t73_tops_2])).
% 0.83/0.99  thf('231', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ 
% 0.83/0.99           (sk_D_1 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_A @ sk_B)))
% 0.83/0.99          != (k2_pre_topc @ sk_B @ 
% 0.83/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (sk_D_1 @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                sk_A @ sk_B))))
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | (v2_struct_0 @ sk_B)
% 0.83/0.99        | ~ (v2_pre_topc @ sk_B)
% 0.83/0.99        | ~ (l1_pre_topc @ sk_B)
% 0.83/0.99        | ~ (v1_funct_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99        | ~ (v1_funct_2 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/0.99        | ~ (m1_subset_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             (k1_zfmisc_1 @ 
% 0.83/0.99              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | ~ (v2_funct_1 @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            != (k2_struct_0 @ sk_A))
% 0.83/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ~ (l1_pre_topc @ sk_A)
% 0.83/0.99        | ~ (v2_pre_topc @ sk_A))),
% 0.83/0.99      inference('sup-', [status(thm)], ['229', '230'])).
% 0.83/0.99  thf('232', plain, ((v2_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('233', plain, ((l1_pre_topc @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('234', plain,
% 0.83/0.99      ((v1_funct_1 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/0.99      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/0.99  thf('235', plain,
% 0.83/0.99      ((v1_funct_2 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/0.99      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/0.99  thf('236', plain,
% 0.83/0.99      ((m1_subset_1 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/0.99      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/0.99  thf('237', plain,
% 0.83/0.99      (((v2_funct_1 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['195', '206'])).
% 0.83/0.99  thf('238', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('239', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('240', plain,
% 0.83/0.99      ((v2_funct_1 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['237', '238', '239'])).
% 0.83/0.99  thf('241', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99          = (k2_struct_0 @ sk_A)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['154', '167'])).
% 0.83/0.99  thf('242', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('243', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('244', plain,
% 0.83/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99         = (k2_struct_0 @ sk_A))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['241', '242', '243'])).
% 0.83/0.99  thf('245', plain,
% 0.83/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99          = (k2_struct_0 @ sk_B)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('sup-', [status(thm)], ['180', '193'])).
% 0.83/0.99  thf('246', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('247', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('248', plain,
% 0.83/0.99      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/0.99         = (k2_struct_0 @ sk_B))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['245', '246', '247'])).
% 0.83/0.99  thf('249', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('250', plain, ((v2_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('251', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ 
% 0.83/0.99           (sk_D_1 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_A @ sk_B)))
% 0.83/0.99          != (k2_pre_topc @ sk_B @ 
% 0.83/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (sk_D_1 @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                sk_A @ sk_B))))
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | (v2_struct_0 @ sk_B)
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.83/0.99        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('demod', [status(thm)],
% 0.83/0.99                ['231', '232', '233', '234', '235', '236', '240', '244', 
% 0.83/0.99                 '248', '249', '250'])).
% 0.83/0.99  thf('252', plain,
% 0.83/0.99      (((v2_struct_0 @ sk_B)
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ 
% 0.83/0.99             (sk_D_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_A @ sk_B)))
% 0.83/0.99            != (k2_pre_topc @ sk_B @ 
% 0.83/0.99                (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C) @ 
% 0.83/0.99                 (sk_D_1 @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  sk_A @ sk_B)))))),
% 0.83/0.99      inference('simplify', [status(thm)], ['251'])).
% 0.83/0.99  thf('253', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('254', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ 
% 0.83/0.99           (sk_D_1 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_A @ sk_B)))
% 0.83/0.99          != (k2_pre_topc @ sk_B @ 
% 0.83/0.99              (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               (sk_D_1 @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                sk_A @ sk_B))))
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A))),
% 0.83/0.99      inference('clc', [status(thm)], ['252', '253'])).
% 0.83/0.99  thf('255', plain,
% 0.83/0.99      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99          (k2_pre_topc @ sk_A @ 
% 0.83/0.99           (sk_D_1 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_A @ sk_B)))
% 0.83/0.99          != (k2_pre_topc @ sk_B @ 
% 0.83/0.99              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ 
% 0.83/0.99               (sk_D_1 @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                sk_A @ sk_B))))
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A)
% 0.83/0.99        | (v3_tops_2 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_B @ sk_A))),
% 0.83/0.99      inference('sup-', [status(thm)], ['216', '254'])).
% 0.83/0.99  thf('256', plain,
% 0.83/0.99      (((v3_tops_2 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99         sk_B @ sk_A)
% 0.83/0.99        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ 
% 0.83/0.99             (sk_D_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_A @ sk_B)))
% 0.83/0.99            != (k2_pre_topc @ sk_B @ 
% 0.83/0.99                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                 sk_C @ 
% 0.83/0.99                 (sk_D_1 @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  sk_A @ sk_B)))))),
% 0.83/0.99      inference('simplify', [status(thm)], ['255'])).
% 0.83/0.99  thf('257', plain,
% 0.83/0.99      ((((m1_subset_1 @ 
% 0.83/0.99          (sk_D_1 @ 
% 0.83/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99           sk_A @ sk_B) @ 
% 0.83/0.99          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99         | (v3_tops_2 @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            sk_B @ sk_A)))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)))),
% 0.83/0.99      inference('clc', [status(thm)], ['209', '210'])).
% 0.83/0.99  thf('258', plain,
% 0.83/0.99      (![X34 : $i]:
% 0.83/0.99         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99              sk_C @ (k2_pre_topc @ sk_A @ X34))
% 0.83/0.99              = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                 (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C @ X34)))
% 0.83/0.99          | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('259', plain,
% 0.83/0.99      ((![X34 : $i]:
% 0.83/0.99          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ (k2_pre_topc @ sk_A @ X34))
% 0.83/0.99               = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C @ X34)))))
% 0.83/0.99         <= ((![X34 : $i]:
% 0.83/0.99                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X34))
% 0.83/0.99                     = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                         (u1_struct_0 @ sk_B) @ sk_C @ X34))))))),
% 0.83/0.99      inference('split', [status(esa)], ['258'])).
% 0.83/0.99  thf('260', plain,
% 0.83/0.99      ((((v3_tops_2 @ 
% 0.83/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99          sk_B @ sk_A)
% 0.83/0.99         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99             sk_C @ 
% 0.83/0.99             (k2_pre_topc @ sk_A @ 
% 0.83/0.99              (sk_D_1 @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99               sk_A @ sk_B)))
% 0.83/0.99             = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                 sk_C @ 
% 0.83/0.99                 (sk_D_1 @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  sk_A @ sk_B))))))
% 0.83/0.99         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/0.99             ((v2_funct_1 @ sk_C)) & 
% 0.83/0.99             (![X34 : $i]:
% 0.83/0.99                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99                 | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                     (u1_struct_0 @ sk_B) @ sk_C @ (k2_pre_topc @ sk_A @ X34))
% 0.83/0.99                     = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                         (u1_struct_0 @ sk_B) @ sk_C @ X34))))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['257', '259'])).
% 0.83/0.99  thf('261', plain,
% 0.83/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99          = (k2_struct_0 @ sk_B)))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/0.99  thf('262', plain, (((v2_funct_1 @ sk_C))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/0.99  thf('263', plain,
% 0.83/0.99      ((![X34 : $i]:
% 0.83/0.99          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ (k2_pre_topc @ sk_A @ X34))
% 0.83/0.99               = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C @ X34))))) | 
% 0.83/0.99       ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/0.99      inference('split', [status(esa)], ['258'])).
% 0.83/0.99  thf('264', plain,
% 0.83/0.99      ((![X34 : $i]:
% 0.83/0.99          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99               sk_C @ (k2_pre_topc @ sk_A @ X34))
% 0.83/0.99               = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                  (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C @ X34)))))),
% 0.83/0.99      inference('sat_resolution*', [status(thm)],
% 0.83/0.99                ['33', '35', '48', '62', '74', '146', '263'])).
% 0.83/0.99  thf('265', plain,
% 0.83/0.99      (((v3_tops_2 @ 
% 0.83/0.99         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99         sk_B @ sk_A)
% 0.83/0.99        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ 
% 0.83/0.99             (sk_D_1 @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              sk_A @ sk_B)))
% 0.83/0.99            = (k2_pre_topc @ sk_B @ 
% 0.83/0.99               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                sk_C @ 
% 0.83/0.99                (sk_D_1 @ 
% 0.83/0.99                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                  sk_C) @ 
% 0.83/0.99                 sk_A @ sk_B)))))),
% 0.83/0.99      inference('simpl_trail', [status(thm)], ['260', '261', '262', '264'])).
% 0.83/0.99  thf('266', plain,
% 0.83/0.99      ((v3_tops_2 @ 
% 0.83/0.99        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99        sk_B @ sk_A)),
% 0.83/0.99      inference('clc', [status(thm)], ['256', '265'])).
% 0.83/0.99  thf('267', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         ((v2_struct_0 @ sk_B)
% 0.83/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/0.99          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99              (k2_pre_topc @ sk_A @ X0))
% 0.83/0.99              = (k2_pre_topc @ sk_B @ 
% 0.83/0.99                 (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/0.99                   sk_C) @ 
% 0.83/0.99                  X0))))),
% 0.83/0.99      inference('demod', [status(thm)], ['153', '266'])).
% 0.83/0.99  thf('268', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('269', plain,
% 0.83/0.99      (![X0 : $i]:
% 0.83/0.99         (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ X0))
% 0.83/0.99            = (k2_pre_topc @ sk_B @ 
% 0.83/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                X0)))
% 0.83/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/0.99      inference('clc', [status(thm)], ['267', '268'])).
% 0.83/0.99  thf('270', plain,
% 0.83/0.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99            (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/0.99            = (k2_pre_topc @ sk_B @ 
% 0.83/0.99               (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99                (sk_D @ sk_C @ sk_B @ sk_A)))))),
% 0.83/0.99      inference('sup-', [status(thm)], ['152', '269'])).
% 0.83/0.99  thf('271', plain,
% 0.83/0.99      ((m1_subset_1 @ sk_C @ 
% 0.83/0.99        (k1_zfmisc_1 @ 
% 0.83/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('272', plain,
% 0.83/0.99      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.83/0.99         (~ (l1_pre_topc @ X3)
% 0.83/0.99          | ((k1_relset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4)
% 0.83/0.99              != (k2_struct_0 @ X5))
% 0.83/0.99          | ((k2_relset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4)
% 0.83/0.99              != (k2_struct_0 @ X3))
% 0.83/0.99          | ~ (v2_funct_1 @ X4)
% 0.83/0.99          | ~ (v5_pre_topc @ X4 @ X5 @ X3)
% 0.83/0.99          | ~ (v5_pre_topc @ 
% 0.83/0.99               (k2_tops_2 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4) @ 
% 0.83/0.99               X3 @ X5)
% 0.83/0.99          | (v3_tops_2 @ X4 @ X5 @ X3)
% 0.83/0.99          | ~ (m1_subset_1 @ X4 @ 
% 0.83/0.99               (k1_zfmisc_1 @ 
% 0.83/0.99                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.83/0.99          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.83/0.99          | ~ (v1_funct_1 @ X4)
% 0.83/0.99          | ~ (l1_pre_topc @ X5))),
% 0.83/0.99      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.83/0.99  thf('273', plain,
% 0.83/0.99      ((~ (l1_pre_topc @ sk_A)
% 0.83/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.83/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/0.99        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | ~ (v5_pre_topc @ 
% 0.83/0.99             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/0.99             sk_B @ sk_A)
% 0.83/0.99        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.83/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_B))
% 0.83/0.99        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/0.99            != (k2_struct_0 @ sk_A))
% 0.83/0.99        | ~ (l1_pre_topc @ sk_B))),
% 0.83/0.99      inference('sup-', [status(thm)], ['271', '272'])).
% 0.83/0.99  thf('274', plain, ((l1_pre_topc @ sk_A)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('275', plain, ((v1_funct_1 @ sk_C)),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('276', plain,
% 0.83/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/0.99  thf('277', plain,
% 0.83/0.99      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00         = (k2_struct_0 @ sk_A))),
% 0.83/1.00      inference('clc', [status(thm)], ['36', '44'])).
% 0.83/1.00  thf('278', plain, ((l1_pre_topc @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('279', plain,
% 0.83/1.00      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (v5_pre_topc @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A)
% 0.83/1.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.00        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00            != (k2_struct_0 @ sk_B))
% 0.83/1.00        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.83/1.00      inference('demod', [status(thm)],
% 0.83/1.00                ['273', '274', '275', '276', '277', '278'])).
% 0.83/1.00  thf('280', plain,
% 0.83/1.00      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00          != (k2_struct_0 @ sk_B))
% 0.83/1.00        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (v5_pre_topc @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A)
% 0.83/1.00        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('simplify', [status(thm)], ['279'])).
% 0.83/1.00  thf('281', plain, (((v2_funct_1 @ sk_C)) <= (((v2_funct_1 @ sk_C)))),
% 0.83/1.00      inference('split', [status(esa)], ['12'])).
% 0.83/1.00  thf('282', plain, (((v2_funct_1 @ sk_C))),
% 0.83/1.00      inference('sat_resolution*', [status(thm)],
% 0.83/1.00                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/1.00  thf('283', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['281', '282'])).
% 0.83/1.00  thf('284', plain,
% 0.83/1.00      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00          != (k2_struct_0 @ sk_B))
% 0.83/1.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (v5_pre_topc @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A)
% 0.83/1.00        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('demod', [status(thm)], ['280', '283'])).
% 0.83/1.00  thf('285', plain,
% 0.83/1.00      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00          = (k2_struct_0 @ sk_B)))
% 0.83/1.00         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                sk_C) = (k2_struct_0 @ sk_B))))),
% 0.83/1.00      inference('split', [status(esa)], ['14'])).
% 0.83/1.00  thf('286', plain,
% 0.83/1.00      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00          = (k2_struct_0 @ sk_B)))),
% 0.83/1.00      inference('sat_resolution*', [status(thm)],
% 0.83/1.00                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/1.00  thf('287', plain,
% 0.83/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00         = (k2_struct_0 @ sk_B))),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['285', '286'])).
% 0.83/1.00  thf('288', plain,
% 0.83/1.00      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/1.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (v5_pre_topc @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A)
% 0.83/1.00        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('demod', [status(thm)], ['284', '287'])).
% 0.83/1.00  thf('289', plain,
% 0.83/1.00      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (v5_pre_topc @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A)
% 0.83/1.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('simplify', [status(thm)], ['288'])).
% 0.83/1.00  thf('290', plain,
% 0.83/1.00      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B))
% 0.83/1.00         <= (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B)))),
% 0.83/1.00      inference('split', [status(esa)], ['34'])).
% 0.83/1.00  thf('291', plain, (~ ((v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('sat_resolution*', [status(thm)],
% 0.83/1.00                ['33', '35', '48', '62', '74', '146'])).
% 0.83/1.00  thf('292', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['290', '291'])).
% 0.83/1.00  thf('293', plain,
% 0.83/1.00      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (v5_pre_topc @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A))),
% 0.83/1.00      inference('clc', [status(thm)], ['289', '292'])).
% 0.83/1.00  thf('294', plain,
% 0.83/1.00      ((m1_subset_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/1.00  thf('295', plain,
% 0.83/1.00      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.83/1.00         (~ (l1_pre_topc @ X3)
% 0.83/1.00          | ~ (v3_tops_2 @ X4 @ X5 @ X3)
% 0.83/1.00          | (v5_pre_topc @ X4 @ X5 @ X3)
% 0.83/1.00          | ~ (m1_subset_1 @ X4 @ 
% 0.83/1.00               (k1_zfmisc_1 @ 
% 0.83/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.83/1.00          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.83/1.00          | ~ (v1_funct_1 @ X4)
% 0.83/1.00          | ~ (l1_pre_topc @ X5))),
% 0.83/1.00      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.83/1.00  thf('296', plain,
% 0.83/1.00      ((~ (l1_pre_topc @ sk_B)
% 0.83/1.00        | ~ (v1_funct_1 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00        | ~ (v1_funct_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.00        | (v5_pre_topc @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00           sk_B @ sk_A)
% 0.83/1.00        | ~ (v3_tops_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A)
% 0.83/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.00      inference('sup-', [status(thm)], ['294', '295'])).
% 0.83/1.00  thf('297', plain, ((l1_pre_topc @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('298', plain,
% 0.83/1.00      ((v1_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/1.00      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/1.00  thf('299', plain,
% 0.83/1.00      ((v1_funct_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/1.00  thf('300', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('301', plain,
% 0.83/1.00      (((v5_pre_topc @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00         sk_B @ sk_A)
% 0.83/1.00        | ~ (v3_tops_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['296', '297', '298', '299', '300'])).
% 0.83/1.00  thf('302', plain,
% 0.83/1.00      ((v3_tops_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        sk_B @ sk_A)),
% 0.83/1.00      inference('clc', [status(thm)], ['256', '265'])).
% 0.83/1.00  thf('303', plain,
% 0.83/1.00      ((v5_pre_topc @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        sk_B @ sk_A)),
% 0.83/1.00      inference('demod', [status(thm)], ['301', '302'])).
% 0.83/1.00  thf('304', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['293', '303'])).
% 0.83/1.00  thf('305', plain,
% 0.83/1.00      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['270', '304'])).
% 0.83/1.00  thf('306', plain,
% 0.83/1.00      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.83/1.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('clc', [status(thm)], ['9', '10'])).
% 0.83/1.00  thf('307', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         (~ (l1_pre_topc @ X0)
% 0.83/1.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.83/1.00          | (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 0.83/1.00             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.83/1.00      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.83/1.00  thf('308', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.83/1.00           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.00      inference('sup-', [status(thm)], ['306', '307'])).
% 0.83/1.00  thf('309', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('310', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.83/1.00           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['308', '309'])).
% 0.83/1.00  thf('311', plain,
% 0.83/1.00      ((![X0 : $i]:
% 0.83/1.00          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00           | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               sk_C @ X0)
% 0.83/1.00               = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                   sk_C) @ 
% 0.83/1.00                  X0))))
% 0.83/1.00         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/1.00             ((v2_funct_1 @ sk_C)))),
% 0.83/1.00      inference('sup-', [status(thm)], ['13', '29'])).
% 0.83/1.00  thf('312', plain,
% 0.83/1.00      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00         | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00             = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00                (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A))))))
% 0.83/1.00         <= ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                sk_C) = (k2_struct_0 @ sk_B))) & 
% 0.83/1.00             ((v2_funct_1 @ sk_C)))),
% 0.83/1.00      inference('sup-', [status(thm)], ['310', '311'])).
% 0.83/1.00  thf('313', plain,
% 0.83/1.00      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.00          = (k2_struct_0 @ sk_B)))),
% 0.83/1.00      inference('sat_resolution*', [status(thm)],
% 0.83/1.00                ['33', '35', '48', '62', '74', '146', '147'])).
% 0.83/1.00  thf('314', plain, (((v2_funct_1 @ sk_C))),
% 0.83/1.00      inference('sat_resolution*', [status(thm)],
% 0.83/1.00                ['33', '35', '48', '62', '74', '146', '149'])).
% 0.83/1.00  thf('315', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00            (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00            = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00               (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))))),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['312', '313', '314'])).
% 0.83/1.00  thf('316', plain,
% 0.83/1.00      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00          (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00          = (k2_pre_topc @ sk_B @ 
% 0.83/1.00             (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00              (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.83/1.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('sup+', [status(thm)], ['305', '315'])).
% 0.83/1.00  thf('317', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['293', '303'])).
% 0.83/1.00  thf('318', plain,
% 0.83/1.00      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['316', '317'])).
% 0.83/1.00  thf('319', plain,
% 0.83/1.00      ((((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00          (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00          = (k2_pre_topc @ sk_B @ 
% 0.83/1.00             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00              sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.83/1.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('sup+', [status(thm)], ['151', '318'])).
% 0.83/1.00  thf('320', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['293', '303'])).
% 0.83/1.00  thf('321', plain,
% 0.83/1.00      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['319', '320'])).
% 0.83/1.00  thf('322', plain,
% 0.83/1.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/1.00         ((v2_struct_0 @ X9)
% 0.83/1.00          | ~ (v2_pre_topc @ X9)
% 0.83/1.00          | ~ (l1_pre_topc @ X9)
% 0.83/1.00          | ~ (r1_tarski @ 
% 0.83/1.00               (k7_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10 @ 
% 0.83/1.00                (k2_pre_topc @ X11 @ (sk_D @ X10 @ X9 @ X11))) @ 
% 0.83/1.00               (k2_pre_topc @ X9 @ 
% 0.83/1.00                (k7_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ 
% 0.83/1.00                 X10 @ (sk_D @ X10 @ X9 @ X11))))
% 0.83/1.00          | (v5_pre_topc @ X10 @ X11 @ X9)
% 0.83/1.00          | ~ (m1_subset_1 @ X10 @ 
% 0.83/1.00               (k1_zfmisc_1 @ 
% 0.83/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.83/1.00          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.83/1.00          | ~ (v1_funct_1 @ X10)
% 0.83/1.00          | ~ (l1_pre_topc @ X11)
% 0.83/1.00          | ~ (v2_pre_topc @ X11))),
% 0.83/1.00      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.83/1.00  thf('323', plain,
% 0.83/1.00      ((~ (r1_tarski @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.83/1.00        | ~ (v2_pre_topc @ sk_A)
% 0.83/1.00        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.00        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.00        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.00        | ~ (m1_subset_1 @ sk_C @ 
% 0.83/1.00             (k1_zfmisc_1 @ 
% 0.83/1.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.83/1.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ~ (l1_pre_topc @ sk_B)
% 0.83/1.00        | ~ (v2_pre_topc @ sk_B)
% 0.83/1.00        | (v2_struct_0 @ sk_B))),
% 0.83/1.00      inference('sup-', [status(thm)], ['321', '322'])).
% 0.83/1.00  thf('324', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('325', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('326', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('327', plain,
% 0.83/1.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('328', plain,
% 0.83/1.00      ((m1_subset_1 @ sk_C @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('329', plain, ((l1_pre_topc @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('330', plain, ((v2_pre_topc @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('331', plain,
% 0.83/1.00      ((~ (r1_tarski @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.83/1.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | (v2_struct_0 @ sk_B))),
% 0.83/1.00      inference('demod', [status(thm)],
% 0.83/1.00                ['323', '324', '325', '326', '327', '328', '329', '330'])).
% 0.83/1.00  thf('332', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['293', '303'])).
% 0.83/1.00  thf('333', plain,
% 0.83/1.00      (((v2_struct_0 @ sk_B)
% 0.83/1.00        | ~ (r1_tarski @ 
% 0.83/1.00             (k2_pre_topc @ sk_B @ 
% 0.83/1.00              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.83/1.00             (k2_pre_topc @ sk_B @ 
% 0.83/1.00              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)))))),
% 0.83/1.00      inference('clc', [status(thm)], ['331', '332'])).
% 0.83/1.00  thf('334', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('335', plain,
% 0.83/1.00      (~ (r1_tarski @ 
% 0.83/1.00          (k2_pre_topc @ sk_B @ 
% 0.83/1.00           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00            (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.83/1.00          (k2_pre_topc @ sk_B @ 
% 0.83/1.00           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00            (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['333', '334'])).
% 0.83/1.00  thf('336', plain,
% 0.83/1.00      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.83/1.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('clc', [status(thm)], ['9', '10'])).
% 0.83/1.00  thf('337', plain,
% 0.83/1.00      ((m1_subset_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/1.00  thf('338', plain,
% 0.83/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.00         ((m1_subset_1 @ (k2_tops_2 @ X6 @ X7 @ X8) @ 
% 0.83/1.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.83/1.00          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.83/1.00          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.83/1.00          | ~ (v1_funct_1 @ X8))),
% 0.83/1.00      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.83/1.00  thf('339', plain,
% 0.83/1.00      ((~ (v1_funct_1 @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00        | ~ (v1_funct_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.00        | (m1_subset_1 @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00           (k1_zfmisc_1 @ 
% 0.83/1.00            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.83/1.00      inference('sup-', [status(thm)], ['337', '338'])).
% 0.83/1.00  thf('340', plain,
% 0.83/1.00      ((v1_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/1.00      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/1.00  thf('341', plain,
% 0.83/1.00      ((v1_funct_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/1.00  thf('342', plain,
% 0.83/1.00      ((m1_subset_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.00      inference('demod', [status(thm)], ['339', '340', '341'])).
% 0.83/1.00  thf('343', plain,
% 0.83/1.00      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.83/1.00         ((v2_struct_0 @ X9)
% 0.83/1.00          | ~ (v2_pre_topc @ X9)
% 0.83/1.00          | ~ (l1_pre_topc @ X9)
% 0.83/1.00          | ~ (v5_pre_topc @ X10 @ X11 @ X9)
% 0.83/1.00          | (r1_tarski @ 
% 0.83/1.00             (k7_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10 @ 
% 0.83/1.00              (k2_pre_topc @ X11 @ X12)) @ 
% 0.83/1.00             (k2_pre_topc @ X9 @ 
% 0.83/1.00              (k7_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10 @ 
% 0.83/1.00               X12)))
% 0.83/1.00          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.83/1.00          | ~ (m1_subset_1 @ X10 @ 
% 0.83/1.00               (k1_zfmisc_1 @ 
% 0.83/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.83/1.00          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.83/1.00          | ~ (v1_funct_1 @ X10)
% 0.83/1.00          | ~ (l1_pre_topc @ X11)
% 0.83/1.00          | ~ (v2_pre_topc @ X11))),
% 0.83/1.00      inference('cnf', [status(esa)], [t57_tops_2])).
% 0.83/1.00  thf('344', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (~ (v2_pre_topc @ sk_A)
% 0.83/1.00          | ~ (l1_pre_topc @ sk_A)
% 0.83/1.00          | ~ (v1_funct_1 @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.83/1.00          | ~ (v1_funct_2 @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00          | (r1_tarski @ 
% 0.83/1.00             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00              (k2_pre_topc @ sk_A @ X0)) @ 
% 0.83/1.00             (k2_pre_topc @ sk_B @ 
% 0.83/1.00              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               X0)))
% 0.83/1.00          | ~ (v5_pre_topc @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               sk_A @ sk_B)
% 0.83/1.00          | ~ (l1_pre_topc @ sk_B)
% 0.83/1.00          | ~ (v2_pre_topc @ sk_B)
% 0.83/1.00          | (v2_struct_0 @ sk_B))),
% 0.83/1.00      inference('sup-', [status(thm)], ['342', '343'])).
% 0.83/1.00  thf('345', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('346', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('347', plain,
% 0.83/1.00      ((m1_subset_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/1.00  thf('348', plain,
% 0.83/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.00         ((v1_funct_1 @ (k2_tops_2 @ X6 @ X7 @ X8))
% 0.83/1.00          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.83/1.00          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.83/1.00          | ~ (v1_funct_1 @ X8))),
% 0.83/1.00      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.83/1.00  thf('349', plain,
% 0.83/1.00      ((~ (v1_funct_1 @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00        | ~ (v1_funct_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.00        | (v1_funct_1 @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.83/1.00      inference('sup-', [status(thm)], ['347', '348'])).
% 0.83/1.00  thf('350', plain,
% 0.83/1.00      ((v1_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/1.00      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/1.00  thf('351', plain,
% 0.83/1.00      ((v1_funct_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/1.00  thf('352', plain,
% 0.83/1.00      ((v1_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.83/1.00      inference('demod', [status(thm)], ['349', '350', '351'])).
% 0.83/1.00  thf('353', plain,
% 0.83/1.00      ((m1_subset_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/1.00  thf('354', plain,
% 0.83/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.00         ((v1_funct_2 @ (k2_tops_2 @ X6 @ X7 @ X8) @ X7 @ X6)
% 0.83/1.00          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.83/1.00          | ~ (v1_funct_2 @ X8 @ X6 @ X7)
% 0.83/1.00          | ~ (v1_funct_1 @ X8))),
% 0.83/1.00      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.83/1.00  thf('355', plain,
% 0.83/1.00      ((~ (v1_funct_1 @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00        | ~ (v1_funct_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.00        | (v1_funct_2 @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.83/1.00      inference('sup-', [status(thm)], ['353', '354'])).
% 0.83/1.00  thf('356', plain,
% 0.83/1.00      ((v1_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/1.00      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/1.00  thf('357', plain,
% 0.83/1.00      ((v1_funct_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/1.00  thf('358', plain,
% 0.83/1.00      ((v1_funct_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.00      inference('demod', [status(thm)], ['355', '356', '357'])).
% 0.83/1.00  thf('359', plain, ((l1_pre_topc @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('360', plain, ((v2_pre_topc @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('361', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00          | (r1_tarski @ 
% 0.83/1.00             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00              (k2_pre_topc @ sk_A @ X0)) @ 
% 0.83/1.00             (k2_pre_topc @ sk_B @ 
% 0.83/1.00              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               X0)))
% 0.83/1.00          | ~ (v5_pre_topc @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               sk_A @ sk_B)
% 0.83/1.00          | (v2_struct_0 @ sk_B))),
% 0.83/1.00      inference('demod', [status(thm)],
% 0.83/1.00                ['344', '345', '346', '352', '358', '359', '360'])).
% 0.83/1.00  thf('362', plain,
% 0.83/1.00      ((m1_subset_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/1.00  thf('363', plain,
% 0.83/1.00      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.83/1.00         (~ (l1_pre_topc @ X3)
% 0.83/1.00          | ~ (v3_tops_2 @ X4 @ X5 @ X3)
% 0.83/1.00          | (v5_pre_topc @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X4) @ X3 @ 
% 0.83/1.00             X5)
% 0.83/1.00          | ~ (m1_subset_1 @ X4 @ 
% 0.83/1.00               (k1_zfmisc_1 @ 
% 0.83/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.83/1.00          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.83/1.00          | ~ (v1_funct_1 @ X4)
% 0.83/1.00          | ~ (l1_pre_topc @ X5))),
% 0.83/1.00      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.83/1.00  thf('364', plain,
% 0.83/1.00      ((~ (l1_pre_topc @ sk_B)
% 0.83/1.00        | ~ (v1_funct_1 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00        | ~ (v1_funct_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.00        | (v5_pre_topc @ 
% 0.83/1.00           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00           sk_A @ sk_B)
% 0.83/1.00        | ~ (v3_tops_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A)
% 0.83/1.00        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.00      inference('sup-', [status(thm)], ['362', '363'])).
% 0.83/1.00  thf('365', plain, ((l1_pre_topc @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('366', plain,
% 0.83/1.00      ((v1_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/1.00      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/1.00  thf('367', plain,
% 0.83/1.00      ((v1_funct_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/1.00  thf('368', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('369', plain,
% 0.83/1.00      (((v5_pre_topc @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00         sk_A @ sk_B)
% 0.83/1.00        | ~ (v3_tops_2 @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             sk_B @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['364', '365', '366', '367', '368'])).
% 0.83/1.00  thf('370', plain,
% 0.83/1.00      ((v3_tops_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        sk_B @ sk_A)),
% 0.83/1.00      inference('clc', [status(thm)], ['256', '265'])).
% 0.83/1.00  thf('371', plain,
% 0.83/1.00      ((v5_pre_topc @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00        sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['369', '370'])).
% 0.83/1.00  thf('372', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00          | (r1_tarski @ 
% 0.83/1.00             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00              (k2_pre_topc @ sk_A @ X0)) @ 
% 0.83/1.00             (k2_pre_topc @ sk_B @ 
% 0.83/1.00              (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               X0)))
% 0.83/1.00          | (v2_struct_0 @ sk_B))),
% 0.83/1.00      inference('demod', [status(thm)], ['361', '371'])).
% 0.83/1.00  thf('373', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('374', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         ((r1_tarski @ 
% 0.83/1.00           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00            (k2_pre_topc @ sk_A @ X0)) @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00             X0)))
% 0.83/1.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['372', '373'])).
% 0.83/1.00  thf('375', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | (r1_tarski @ 
% 0.83/1.00           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00            (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00             (sk_D @ sk_C @ sk_B @ sk_A)))))),
% 0.83/1.00      inference('sup-', [status(thm)], ['336', '374'])).
% 0.83/1.00  thf('376', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.83/1.00           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['308', '309'])).
% 0.83/1.00  thf('377', plain,
% 0.83/1.00      ((m1_subset_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (k1_zfmisc_1 @ 
% 0.83/1.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.83/1.00  thf(t68_tops_2, axiom,
% 0.83/1.00    (![A:$i]:
% 0.83/1.00     ( ( l1_struct_0 @ A ) =>
% 0.83/1.00       ( ![B:$i]:
% 0.83/1.00         ( ( l1_struct_0 @ B ) =>
% 0.83/1.00           ( ![C:$i]:
% 0.83/1.00             ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.00                 ( m1_subset_1 @
% 0.83/1.00                   C @ 
% 0.83/1.00                   ( k1_zfmisc_1 @
% 0.83/1.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.00               ( ![D:$i]:
% 0.83/1.00                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.83/1.00                   ( ( ( ( k2_relset_1 @
% 0.83/1.00                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/1.00                         ( k2_struct_0 @ B ) ) & 
% 0.83/1.00                       ( v2_funct_1 @ C ) ) =>
% 0.83/1.00                     ( ( k8_relset_1 @
% 0.83/1.00                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.83/1.00                       ( k7_relset_1 @
% 0.83/1.00                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.00                         ( k2_tops_2 @
% 0.83/1.00                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.83/1.00                         D ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.00  thf('378', plain,
% 0.83/1.00      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.00         (~ (l1_struct_0 @ X23)
% 0.83/1.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.83/1.00          | ((k8_relset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23) @ X26 @ 
% 0.83/1.00              X24)
% 0.83/1.00              = (k7_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X25) @ 
% 0.83/1.00                 (k2_tops_2 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23) @ X26) @ 
% 0.83/1.00                 X24))
% 0.83/1.00          | ~ (v2_funct_1 @ X26)
% 0.83/1.00          | ((k2_relset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23) @ X26)
% 0.83/1.00              != (k2_struct_0 @ X23))
% 0.83/1.00          | ~ (m1_subset_1 @ X26 @ 
% 0.83/1.00               (k1_zfmisc_1 @ 
% 0.83/1.00                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))))
% 0.83/1.00          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X23))
% 0.83/1.00          | ~ (v1_funct_1 @ X26)
% 0.83/1.00          | ~ (l1_struct_0 @ X25))),
% 0.83/1.00      inference('cnf', [status(esa)], [t68_tops_2])).
% 0.83/1.00  thf('379', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (~ (l1_struct_0 @ sk_B)
% 0.83/1.00          | ~ (v1_funct_1 @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00          | ~ (v1_funct_2 @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.00          | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00              != (k2_struct_0 @ sk_A))
% 0.83/1.00          | ~ (v2_funct_1 @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00              X0)
% 0.83/1.00              = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                 (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                   sk_C)) @ 
% 0.83/1.00                 X0))
% 0.83/1.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00          | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.00      inference('sup-', [status(thm)], ['377', '378'])).
% 0.83/1.00  thf('380', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.00      inference('sup-', [status(thm)], ['24', '25'])).
% 0.83/1.00  thf('381', plain,
% 0.83/1.00      ((v1_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/1.00      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.83/1.00  thf('382', plain,
% 0.83/1.00      ((v1_funct_2 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.83/1.00      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.83/1.00  thf('383', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.00      inference('sup-', [status(thm)], ['19', '20'])).
% 0.83/1.00  thf('384', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00            != (k2_struct_0 @ sk_A))
% 0.83/1.00          | ~ (v2_funct_1 @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00              X0)
% 0.83/1.00              = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                 (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                   sk_C)) @ 
% 0.83/1.00                 X0))
% 0.83/1.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['379', '380', '381', '382', '383'])).
% 0.83/1.00  thf('385', plain,
% 0.83/1.00      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.00         = (k2_struct_0 @ sk_A))),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['241', '242', '243'])).
% 0.83/1.00  thf('386', plain,
% 0.83/1.00      ((v2_funct_1 @ 
% 0.83/1.00        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['237', '238', '239'])).
% 0.83/1.00  thf('387', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.83/1.00          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00              X0)
% 0.83/1.00              = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                 (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                   sk_C)) @ 
% 0.83/1.00                 X0))
% 0.83/1.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['384', '385', '386'])).
% 0.83/1.00  thf('388', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00              X0)
% 0.83/1.00              = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                 (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                   sk_C)) @ 
% 0.83/1.00                 X0)))),
% 0.83/1.00      inference('simplify', [status(thm)], ['387'])).
% 0.83/1.00  thf('389', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00            (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00            = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))))),
% 0.83/1.00      inference('sup-', [status(thm)], ['376', '388'])).
% 0.83/1.00  thf('390', plain,
% 0.83/1.00      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['270', '304'])).
% 0.83/1.00  thf('391', plain,
% 0.83/1.00      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['316', '317'])).
% 0.83/1.00  thf('392', plain,
% 0.83/1.00      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00            (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['390', '391'])).
% 0.83/1.00  thf('393', plain,
% 0.83/1.00      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['319', '320'])).
% 0.83/1.00  thf('394', plain,
% 0.83/1.00      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['392', '393'])).
% 0.83/1.00  thf('395', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ((k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00            = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))))),
% 0.83/1.00      inference('demod', [status(thm)], ['389', '394'])).
% 0.83/1.00  thf('396', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['293', '303'])).
% 0.83/1.00  thf('397', plain,
% 0.83/1.00      (((k2_pre_topc @ sk_B @ 
% 0.83/1.00         (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00          (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00            (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['395', '396'])).
% 0.83/1.00  thf('398', plain,
% 0.83/1.00      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.83/1.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.83/1.00      inference('clc', [status(thm)], ['9', '10'])).
% 0.83/1.00  thf('399', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.00          | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00              X0)
% 0.83/1.00              = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                 (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00                   sk_C)) @ 
% 0.83/1.00                 X0)))),
% 0.83/1.00      inference('simplify', [status(thm)], ['387'])).
% 0.83/1.00  thf('400', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | ((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00            (sk_D @ sk_C @ sk_B @ sk_A))
% 0.83/1.00            = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00               (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('sup-', [status(thm)], ['398', '399'])).
% 0.83/1.00  thf('401', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['293', '303'])).
% 0.83/1.00  thf('402', plain,
% 0.83/1.00      (((k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00         (sk_D @ sk_C @ sk_B @ sk_A))
% 0.83/1.00         = (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00            (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.00            (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.83/1.00      inference('clc', [status(thm)], ['400', '401'])).
% 0.83/1.00  thf('403', plain,
% 0.83/1.00      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['316', '317'])).
% 0.83/1.00  thf('404', plain,
% 0.83/1.00      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00         (k2_pre_topc @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['319', '320'])).
% 0.83/1.00  thf('405', plain,
% 0.83/1.00      (((k2_pre_topc @ sk_B @ 
% 0.83/1.00         (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00          (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.83/1.00         = (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.00             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.83/1.00             (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('demod', [status(thm)], ['403', '404'])).
% 0.83/1.00  thf('406', plain,
% 0.83/1.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.83/1.00        | (r1_tarski @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.83/1.00           (k2_pre_topc @ sk_B @ 
% 0.83/1.00            (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.00             sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)))))),
% 0.83/1.00      inference('demod', [status(thm)], ['375', '397', '402', '405'])).
% 0.83/1.00  thf('407', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.83/1.00      inference('demod', [status(thm)], ['293', '303'])).
% 0.83/1.00  thf('408', plain,
% 0.83/1.00      ((r1_tarski @ 
% 0.83/1.00        (k2_pre_topc @ sk_B @ 
% 0.83/1.00         (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00          (sk_D @ sk_C @ sk_B @ sk_A))) @ 
% 0.83/1.00        (k2_pre_topc @ sk_B @ 
% 0.83/1.00         (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.00          (sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.83/1.00      inference('clc', [status(thm)], ['406', '407'])).
% 0.83/1.00  thf('409', plain, ($false), inference('demod', [status(thm)], ['335', '408'])).
% 0.83/1.00  
% 0.83/1.00  % SZS output end Refutation
% 0.83/1.00  
% 0.83/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
