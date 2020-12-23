%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Hg1xDq0ck

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:41 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 159 expanded)
%              Number of leaves         :   38 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  911 (3727 expanded)
%              Number of equality atoms :   11 (  61 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t25_compts_1,conjecture,(
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
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v5_pre_topc @ C @ A @ B ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( v4_pre_topc @ D @ A )
                       => ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_compts_1])).

thf('0',plain,(
    ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                 => ( ( ( v5_pre_topc @ D @ A @ C )
                      & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D )
                        = ( k2_struct_0 @ C ) )
                      & ( v2_compts_1 @ B @ A ) )
                   => ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) @ X22 @ X20 ) @ X23 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) @ X22 )
       != ( k2_struct_0 @ X23 ) )
      | ~ ( v5_pre_topc @ X22 @ X21 @ X23 )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t24_compts_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_compts_1 @ sk_D_1 @ sk_A )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf(t10_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( ~ ( v1_compts_1 @ X14 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t18_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_compts_1 @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ( v2_compts_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v2_compts_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('38',plain,(
    v4_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v2_compts_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','37','38','39','40'])).

thf('42',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('44',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_compts_1 @ sk_D_1 @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X9 @ X10 @ X8 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( v2_compts_1 @ X15 @ X16 )
      | ~ ( v8_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Hg1xDq0ck
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 273 iterations in 0.165s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.62  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.42/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.42/0.62  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.42/0.62  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.42/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.62  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.42/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(t25_compts_1, conjecture,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.62             ( l1_pre_topc @ B ) ) =>
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.62                 ( m1_subset_1 @
% 0.42/0.62                   C @ 
% 0.42/0.62                   ( k1_zfmisc_1 @
% 0.42/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.62               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.42/0.62                   ( ( k2_relset_1 @
% 0.42/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.42/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.42/0.62                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.42/0.62                 ( ![D:$i]:
% 0.42/0.62                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62                     ( ( v4_pre_topc @ D @ A ) =>
% 0.42/0.62                       ( v4_pre_topc @
% 0.42/0.62                         ( k7_relset_1 @
% 0.42/0.62                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.42/0.62                         B ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i]:
% 0.42/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62          ( ![B:$i]:
% 0.42/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.62                ( l1_pre_topc @ B ) ) =>
% 0.42/0.62              ( ![C:$i]:
% 0.42/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.62                    ( v1_funct_2 @
% 0.42/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.62                    ( m1_subset_1 @
% 0.42/0.62                      C @ 
% 0.42/0.62                      ( k1_zfmisc_1 @
% 0.42/0.62                        ( k2_zfmisc_1 @
% 0.42/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.62                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.42/0.62                      ( ( k2_relset_1 @
% 0.42/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.42/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.42/0.62                      ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.42/0.62                    ( ![D:$i]:
% 0.42/0.62                      ( ( m1_subset_1 @
% 0.42/0.62                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62                        ( ( v4_pre_topc @ D @ A ) =>
% 0.42/0.62                          ( v4_pre_topc @
% 0.42/0.62                            ( k7_relset_1 @
% 0.42/0.62                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.42/0.62                            B ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t25_compts_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (~ (v4_pre_topc @ 
% 0.42/0.62          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.62           sk_D_1) @ 
% 0.42/0.62          sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t24_compts_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_pre_topc @ C ) ) =>
% 0.42/0.62               ( ![D:$i]:
% 0.42/0.62                 ( ( ( v1_funct_1 @ D ) & 
% 0.42/0.62                     ( v1_funct_2 @
% 0.42/0.62                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.42/0.62                     ( m1_subset_1 @
% 0.42/0.62                       D @ 
% 0.42/0.62                       ( k1_zfmisc_1 @
% 0.42/0.62                         ( k2_zfmisc_1 @
% 0.42/0.62                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.42/0.62                   ( ( ( v5_pre_topc @ D @ A @ C ) & 
% 0.42/0.62                       ( ( k2_relset_1 @
% 0.42/0.62                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D ) =
% 0.42/0.62                         ( k2_struct_0 @ C ) ) & 
% 0.42/0.62                       ( v2_compts_1 @ B @ A ) ) =>
% 0.42/0.62                     ( v2_compts_1 @
% 0.42/0.62                       ( k7_relset_1 @
% 0.42/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ 
% 0.42/0.62                       C ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.62          | ~ (v1_funct_1 @ X22)
% 0.42/0.62          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))
% 0.42/0.62          | ~ (m1_subset_1 @ X22 @ 
% 0.42/0.62               (k1_zfmisc_1 @ 
% 0.42/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))))
% 0.42/0.62          | (v2_compts_1 @ 
% 0.42/0.62             (k7_relset_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23) @ X22 @ 
% 0.42/0.62              X20) @ 
% 0.42/0.62             X23)
% 0.42/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23) @ X22)
% 0.42/0.62              != (k2_struct_0 @ X23))
% 0.42/0.62          | ~ (v5_pre_topc @ X22 @ X21 @ X23)
% 0.42/0.62          | ~ (v2_compts_1 @ X20 @ X21)
% 0.42/0.62          | ~ (l1_pre_topc @ X23)
% 0.42/0.62          | (v2_struct_0 @ X23)
% 0.42/0.62          | ~ (l1_pre_topc @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t24_compts_1])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ sk_A)
% 0.42/0.62          | (v2_struct_0 @ sk_B)
% 0.42/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.62          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.62          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.42/0.62          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.42/0.62              != (k2_struct_0 @ sk_B))
% 0.42/0.62          | (v2_compts_1 @ 
% 0.42/0.62             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.42/0.62              sk_C @ X0) @ 
% 0.42/0.62             sk_B)
% 0.42/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.42/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.62  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('7', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.42/0.62         = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((v2_struct_0 @ sk_B)
% 0.42/0.62          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.62          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.42/0.62          | (v2_compts_1 @ 
% 0.42/0.62             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.42/0.62              sk_C @ X0) @ 
% 0.42/0.62             sk_B)
% 0.42/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['4', '5', '6', '7', '8', '9', '10'])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62          | (v2_compts_1 @ 
% 0.42/0.62             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.42/0.62              sk_C @ X0) @ 
% 0.42/0.62             sk_B)
% 0.42/0.62          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.62          | (v2_struct_0 @ sk_B))),
% 0.42/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (((v2_struct_0 @ sk_B)
% 0.42/0.62        | ~ (v2_compts_1 @ sk_D_1 @ sk_A)
% 0.42/0.62        | (v2_compts_1 @ 
% 0.42/0.62           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.62            sk_D_1) @ 
% 0.42/0.62           sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '12'])).
% 0.42/0.62  thf(t10_compts_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (~ (v1_compts_1 @ X14)
% 0.42/0.62          | (v2_compts_1 @ (k2_struct_0 @ X14) @ X14)
% 0.42/0.62          | ~ (l1_pre_topc @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [t10_compts_1])).
% 0.42/0.62  thf(d3_struct_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X12 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_k2_subset_1, axiom,
% 0.42/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.42/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.42/0.62  thf('18', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.42/0.62  thf('19', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.42/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf(t18_compts_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.42/0.62                   ( v4_pre_topc @ C @ A ) ) =>
% 0.42/0.62                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.62          | ~ (v2_compts_1 @ X17 @ X18)
% 0.42/0.62          | ~ (r1_tarski @ X19 @ X17)
% 0.42/0.62          | ~ (v4_pre_topc @ X19 @ X18)
% 0.42/0.62          | (v2_compts_1 @ X19 @ X18)
% 0.42/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.62          | ~ (l1_pre_topc @ X18)
% 0.42/0.62          | ~ (v2_pre_topc @ X18))),
% 0.42/0.62      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v2_pre_topc @ X0)
% 0.42/0.62          | ~ (l1_pre_topc @ X0)
% 0.42/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.42/0.62          | (v2_compts_1 @ X1 @ X0)
% 0.42/0.62          | ~ (v4_pre_topc @ X1 @ X0)
% 0.42/0.62          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.42/0.62          | ~ (v2_compts_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      ((~ (v2_compts_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.42/0.62        | ~ (r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | ~ (v4_pre_topc @ sk_D_1 @ sk_A)
% 0.42/0.62        | (v2_compts_1 @ sk_D_1 @ sk_A)
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | ~ (v2_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('24', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.42/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf(t7_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62           ( ( ![D:$i]:
% 0.42/0.62               ( ( m1_subset_1 @ D @ A ) =>
% 0.42/0.62                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.42/0.62             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.42/0.62          | (r1_tarski @ X7 @ X5)
% 0.42/0.62          | (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X7)
% 0.42/0.62          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.42/0.62          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.42/0.62          | (r1_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (r2_hidden @ 
% 0.42/0.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_D_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.42/0.62           sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '26'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(l3_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ X3)
% 0.42/0.62          | (r2_hidden @ X2 @ X4)
% 0.42/0.62          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (r2_hidden @ 
% 0.42/0.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_D_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.42/0.62           (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['27', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('33', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.42/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.42/0.62          | (r1_tarski @ X7 @ X5)
% 0.42/0.62          | ~ (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X5)
% 0.42/0.62          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.42/0.62          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.42/0.62          | (r1_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | ~ (r2_hidden @ 
% 0.42/0.62             (sk_D @ (u1_struct_0 @ sk_A) @ sk_D_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.42/0.62             (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['32', '35'])).
% 0.42/0.62  thf('37', plain, ((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('clc', [status(thm)], ['31', '36'])).
% 0.42/0.62  thf('38', plain, ((v4_pre_topc @ sk_D_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      ((~ (v2_compts_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.42/0.62        | (v2_compts_1 @ sk_D_1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['22', '37', '38', '39', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.42/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.42/0.62        | (v2_compts_1 @ sk_D_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '41'])).
% 0.42/0.62  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_l1_pre_topc, axiom,
% 0.42/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.62  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.42/0.62        | (v2_compts_1 @ sk_D_1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['42', '45'])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | ~ (v1_compts_1 @ sk_A)
% 0.42/0.62        | (v2_compts_1 @ sk_D_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['14', '46'])).
% 0.42/0.62  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('49', plain, ((v1_compts_1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('50', plain, ((v2_compts_1 @ sk_D_1 @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (((v2_struct_0 @ sk_B)
% 0.42/0.62        | (v2_compts_1 @ 
% 0.42/0.62           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.62            sk_D_1) @ 
% 0.42/0.62           sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['13', '50'])).
% 0.42/0.62  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      ((v2_compts_1 @ 
% 0.42/0.62        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.62         sk_D_1) @ 
% 0.42/0.62        sk_B)),
% 0.42/0.62      inference('clc', [status(thm)], ['51', '52'])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_k7_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.42/0.62          | (m1_subset_1 @ (k7_relset_1 @ X9 @ X10 @ X8 @ X11) @ 
% 0.42/0.62             (k1_zfmisc_1 @ X10)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (m1_subset_1 @ 
% 0.42/0.62          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.62           X0) @ 
% 0.42/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.42/0.62  thf(t16_compts_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.42/0.62             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.42/0.62          | (v4_pre_topc @ X15 @ X16)
% 0.42/0.62          | ~ (v2_compts_1 @ X15 @ X16)
% 0.42/0.62          | ~ (v8_pre_topc @ X16)
% 0.42/0.62          | ~ (l1_pre_topc @ X16)
% 0.42/0.62          | ~ (v2_pre_topc @ X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v2_pre_topc @ sk_B)
% 0.42/0.62          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.62          | ~ (v8_pre_topc @ sk_B)
% 0.42/0.62          | ~ (v2_compts_1 @ 
% 0.42/0.62               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.42/0.62                sk_C @ X0) @ 
% 0.42/0.62               sk_B)
% 0.42/0.62          | (v4_pre_topc @ 
% 0.42/0.62             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.42/0.62              sk_C @ X0) @ 
% 0.42/0.62             sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('59', plain, ((v2_pre_topc @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('61', plain, ((v8_pre_topc @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v2_compts_1 @ 
% 0.42/0.62             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.42/0.62              sk_C @ X0) @ 
% 0.42/0.62             sk_B)
% 0.42/0.62          | (v4_pre_topc @ 
% 0.42/0.62             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.42/0.62              sk_C @ X0) @ 
% 0.42/0.62             sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      ((v4_pre_topc @ 
% 0.42/0.62        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.42/0.62         sk_D_1) @ 
% 0.42/0.62        sk_B)),
% 0.42/0.62      inference('sup-', [status(thm)], ['53', '62'])).
% 0.42/0.62  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
