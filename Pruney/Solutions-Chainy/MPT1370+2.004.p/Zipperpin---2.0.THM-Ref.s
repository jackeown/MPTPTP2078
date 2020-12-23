%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z8EqT7i4k7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 163 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  841 (3902 expanded)
%              Number of equality atoms :   12 (  65 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,(
    ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v4_pre_topc @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v4_pre_topc @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) @ X18 @ X16 ) @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X19 ) @ X18 )
       != ( k2_struct_0 @ X19 ) )
      | ~ ( v5_pre_topc @ X18 @ X17 @ X19 )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_compts_1])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_compts_1 @ sk_D @ sk_A )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t10_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ~ ( v1_compts_1 @ X10 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

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

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_compts_1 @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( v4_pre_topc @ X15 @ X14 )
      | ( v2_compts_1 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_D @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_D @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_D @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('33',plain,(
    r1_tarski @ sk_D @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v4_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('38',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['26','33','34','35','36','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_compts_1 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_compts_1 @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('48',plain,(
    v2_compts_1 @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X4 @ X5 @ X3 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( v2_compts_1 @ X11 @ X12 )
      | ~ ( v8_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_compts_1 @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    v4_pre_topc @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['6','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z8EqT7i4k7
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 126 iterations in 0.059s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(d3_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf(t25_compts_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.21/0.51                   ( ( k2_relset_1 @
% 0.21/0.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.51                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.51                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                     ( ( v4_pre_topc @ D @ A ) =>
% 0.21/0.51                       ( v4_pre_topc @
% 0.21/0.51                         ( k7_relset_1 @
% 0.21/0.51                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.21/0.51                         B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51                ( l1_pre_topc @ B ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                    ( v1_funct_2 @
% 0.21/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                    ( m1_subset_1 @
% 0.21/0.51                      C @ 
% 0.21/0.51                      ( k1_zfmisc_1 @
% 0.21/0.51                        ( k2_zfmisc_1 @
% 0.21/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.21/0.51                      ( ( k2_relset_1 @
% 0.21/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.51                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.51                      ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.21/0.51                    ( ![D:$i]:
% 0.21/0.51                      ( ( m1_subset_1 @
% 0.21/0.51                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                        ( ( v4_pre_topc @ D @ A ) =>
% 0.21/0.51                          ( v4_pre_topc @
% 0.21/0.51                            ( k7_relset_1 @
% 0.21/0.51                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.21/0.51                            B ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t25_compts_1])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (~ (v4_pre_topc @ 
% 0.21/0.51          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51           sk_D) @ 
% 0.21/0.51          sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((~ (v4_pre_topc @ 
% 0.21/0.51           (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            sk_D) @ 
% 0.21/0.51           sk_B)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('4', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (~ (v4_pre_topc @ 
% 0.21/0.51          (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51           sk_D) @ 
% 0.21/0.51          sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t24_compts_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_pre_topc @ C ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.51                     ( v1_funct_2 @
% 0.21/0.51                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.51                     ( m1_subset_1 @
% 0.21/0.51                       D @ 
% 0.21/0.51                       ( k1_zfmisc_1 @
% 0.21/0.51                         ( k2_zfmisc_1 @
% 0.21/0.51                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.21/0.51                   ( ( ( v5_pre_topc @ D @ A @ C ) & 
% 0.21/0.51                       ( ( k2_relset_1 @
% 0.21/0.51                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D ) =
% 0.21/0.51                         ( k2_struct_0 @ C ) ) & 
% 0.21/0.51                       ( v2_compts_1 @ B @ A ) ) =>
% 0.21/0.51                     ( v2_compts_1 @
% 0.21/0.51                       ( k7_relset_1 @
% 0.21/0.51                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ 
% 0.21/0.51                       C ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.51          | ~ (v1_funct_1 @ X18)
% 0.21/0.51          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19))))
% 0.21/0.51          | (v2_compts_1 @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19) @ X18 @ 
% 0.21/0.51              X16) @ 
% 0.21/0.51             X19)
% 0.21/0.51          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X19) @ X18)
% 0.21/0.51              != (k2_struct_0 @ X19))
% 0.21/0.51          | ~ (v5_pre_topc @ X18 @ X17 @ X19)
% 0.21/0.51          | ~ (v2_compts_1 @ X16 @ X17)
% 0.21/0.51          | ~ (l1_pre_topc @ X19)
% 0.21/0.51          | (v2_struct_0 @ X19)
% 0.21/0.51          | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t24_compts_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.51          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.51              != (k2_struct_0 @ sk_B))
% 0.21/0.51          | (v2_compts_1 @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) @ 
% 0.21/0.51             sk_B)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.51         = (k2_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.21/0.51          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.51          | (v2_compts_1 @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) @ 
% 0.21/0.51             sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['11', '12', '13', '14', '15', '16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v2_compts_1 @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) @ 
% 0.21/0.51             sk_B)
% 0.21/0.51          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v2_compts_1 @ sk_D @ sk_A)
% 0.21/0.51        | (v2_compts_1 @ 
% 0.21/0.51           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            sk_D) @ 
% 0.21/0.51           sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '19'])).
% 0.21/0.51  thf(t10_compts_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X10 : $i]:
% 0.21/0.51         (~ (v1_compts_1 @ X10)
% 0.21/0.51          | (v2_compts_1 @ (k2_struct_0 @ X10) @ X10)
% 0.21/0.51          | ~ (l1_pre_topc @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t10_compts_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X8 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.51          | ~ (l1_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.51  thf(t18_compts_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.21/0.51                   ( v4_pre_topc @ C @ A ) ) =>
% 0.21/0.51                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | ~ (v2_compts_1 @ X13 @ X14)
% 0.21/0.51          | ~ (r1_tarski @ X15 @ X13)
% 0.21/0.51          | ~ (v4_pre_topc @ X15 @ X14)
% 0.21/0.51          | (v2_compts_1 @ X15 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | ~ (l1_pre_topc @ X14)
% 0.21/0.51          | ~ (v2_pre_topc @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_compts_1 @ X1 @ X0)
% 0.21/0.51          | ~ (v4_pre_topc @ X1 @ X0)
% 0.21/0.51          | ~ (r1_tarski @ X1 @ (k2_struct_0 @ X0))
% 0.21/0.51          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.51        | ~ (r1_tarski @ sk_D @ (k2_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v4_pre_topc @ sk_D @ sk_A)
% 0.21/0.51        | (v2_compts_1 @ sk_D @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('30', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((r1_tarski @ sk_D @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['27', '30'])).
% 0.21/0.51  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('33', plain, ((r1_tarski @ sk_D @ (k2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, ((v4_pre_topc @ sk_D @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.51        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '33', '34', '35', '36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v1_compts_1 @ sk_A)
% 0.21/0.51        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '38'])).
% 0.21/0.51  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, ((v1_compts_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain, ((v2_compts_1 @ sk_D @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_compts_1 @ 
% 0.21/0.51           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51            sk_D) @ 
% 0.21/0.51           sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '42'])).
% 0.21/0.51  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((v2_compts_1 @ 
% 0.21/0.51        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51         sk_D) @ 
% 0.21/0.51        sk_B)),
% 0.21/0.51      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((v2_compts_1 @ 
% 0.21/0.51         (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51          sk_D) @ 
% 0.21/0.51         sk_B)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['7', '45'])).
% 0.21/0.51  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((v2_compts_1 @ 
% 0.21/0.51        (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51         sk_D) @ 
% 0.21/0.51        sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_C @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf(dt_k7_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.51          | (m1_subset_1 @ (k7_relset_1 @ X4 @ X5 @ X3 @ X6) @ 
% 0.21/0.51             (k1_zfmisc_1 @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (m1_subset_1 @ 
% 0.21/0.51          (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51           X0) @ 
% 0.21/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf(t16_compts_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.21/0.51             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.51          | (v4_pre_topc @ X11 @ X12)
% 0.21/0.51          | ~ (v2_compts_1 @ X11 @ X12)
% 0.21/0.51          | ~ (v8_pre_topc @ X12)
% 0.21/0.51          | ~ (l1_pre_topc @ X12)
% 0.21/0.51          | ~ (v2_pre_topc @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v8_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v2_compts_1 @ 
% 0.21/0.51               (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                sk_C @ X0) @ 
% 0.21/0.51               sk_B)
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) @ 
% 0.21/0.51             sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain, ((v8_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_compts_1 @ 
% 0.21/0.51             (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) @ 
% 0.21/0.51             sk_B)
% 0.21/0.51          | (v4_pre_topc @ 
% 0.21/0.51             (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51              sk_C @ X0) @ 
% 0.21/0.51             sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((v4_pre_topc @ 
% 0.21/0.51        (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.51         sk_D) @ 
% 0.21/0.51        sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '61'])).
% 0.21/0.51  thf('63', plain, ($false), inference('demod', [status(thm)], ['6', '62'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
