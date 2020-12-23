%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XdubNuBzZc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:41 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 131 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  762 (3282 expanded)
%              Number of equality atoms :   11 (  53 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) @ X19 @ X17 ) @ X20 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) @ X19 )
       != ( k2_struct_0 @ X20 ) )
      | ~ ( v5_pre_topc @ X19 @ X18 @ X20 )
      | ~ ( v2_compts_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    | ~ ( v2_compts_1 @ sk_D @ sk_A )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf(t10_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ~ ( v1_compts_1 @ X11 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_compts_1 @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( v4_pre_topc @ X16 @ X15 )
      | ( v2_compts_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
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
    | ~ ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_D @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v4_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v2_compts_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf('30',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_compts_1 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X6 @ X7 @ X5 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v2_compts_1 @ X12 @ X13 )
      | ~ ( v8_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.06  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XdubNuBzZc
% 0.06/0.24  % Computer   : n021.cluster.edu
% 0.06/0.24  % Model      : x86_64 x86_64
% 0.06/0.24  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.24  % Memory     : 8042.1875MB
% 0.06/0.24  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.24  % CPULimit   : 60
% 0.06/0.24  % DateTime   : Tue Dec  1 12:45:19 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running portfolio for 600 s
% 0.06/0.25  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.06/0.25  % Number of cores: 8
% 0.06/0.25  % Python version: Python 3.6.8
% 0.06/0.25  % Running in FO mode
% 0.10/0.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.10/0.39  % Solved by: fo/fo7.sh
% 0.10/0.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.10/0.39  % done 176 iterations in 0.053s
% 0.10/0.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.10/0.39  % SZS output start Refutation
% 0.10/0.39  thf(sk_C_type, type, sk_C: $i).
% 0.10/0.39  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.10/0.39  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.10/0.39  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.10/0.39  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.10/0.39  thf(sk_D_type, type, sk_D: $i).
% 0.10/0.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.10/0.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.10/0.39  thf(sk_B_type, type, sk_B: $i).
% 0.10/0.39  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.10/0.39  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.10/0.39  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.10/0.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.10/0.39  thf(sk_A_type, type, sk_A: $i).
% 0.10/0.39  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.10/0.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.10/0.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.10/0.39  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.10/0.39  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.10/0.39  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.10/0.39  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.10/0.39  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.10/0.39  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.10/0.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.10/0.39  thf(t25_compts_1, conjecture,
% 0.10/0.39    (![A:$i]:
% 0.10/0.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.10/0.39       ( ![B:$i]:
% 0.10/0.39         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.10/0.39             ( l1_pre_topc @ B ) ) =>
% 0.10/0.39           ( ![C:$i]:
% 0.10/0.39             ( ( ( v1_funct_1 @ C ) & 
% 0.10/0.39                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.10/0.39                 ( m1_subset_1 @
% 0.10/0.39                   C @ 
% 0.10/0.39                   ( k1_zfmisc_1 @
% 0.10/0.39                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.10/0.39               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.10/0.39                   ( ( k2_relset_1 @
% 0.10/0.39                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.10/0.39                     ( k2_struct_0 @ B ) ) & 
% 0.10/0.39                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.10/0.39                 ( ![D:$i]:
% 0.10/0.39                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.10/0.39                     ( ( v4_pre_topc @ D @ A ) =>
% 0.10/0.39                       ( v4_pre_topc @
% 0.10/0.39                         ( k7_relset_1 @
% 0.10/0.39                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.10/0.39                         B ) ) ) ) ) ) ) ) ) ))).
% 0.10/0.39  thf(zf_stmt_0, negated_conjecture,
% 0.10/0.39    (~( ![A:$i]:
% 0.10/0.39        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.10/0.39          ( ![B:$i]:
% 0.10/0.39            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.10/0.39                ( l1_pre_topc @ B ) ) =>
% 0.10/0.39              ( ![C:$i]:
% 0.10/0.39                ( ( ( v1_funct_1 @ C ) & 
% 0.10/0.39                    ( v1_funct_2 @
% 0.10/0.39                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.10/0.39                    ( m1_subset_1 @
% 0.10/0.39                      C @ 
% 0.10/0.39                      ( k1_zfmisc_1 @
% 0.10/0.39                        ( k2_zfmisc_1 @
% 0.10/0.39                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.10/0.39                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.10/0.39                      ( ( k2_relset_1 @
% 0.10/0.39                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.10/0.39                        ( k2_struct_0 @ B ) ) & 
% 0.10/0.39                      ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.10/0.39                    ( ![D:$i]:
% 0.10/0.39                      ( ( m1_subset_1 @
% 0.10/0.39                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.10/0.39                        ( ( v4_pre_topc @ D @ A ) =>
% 0.10/0.39                          ( v4_pre_topc @
% 0.10/0.39                            ( k7_relset_1 @
% 0.10/0.39                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.10/0.39                            B ) ) ) ) ) ) ) ) ) ) )),
% 0.10/0.39    inference('cnf.neg', [status(esa)], [t25_compts_1])).
% 0.10/0.39  thf('0', plain,
% 0.10/0.39      (~ (v4_pre_topc @ 
% 0.10/0.39          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.10/0.39           sk_D) @ 
% 0.10/0.39          sk_B)),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('1', plain,
% 0.10/0.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('2', plain,
% 0.10/0.39      ((m1_subset_1 @ sk_C @ 
% 0.10/0.39        (k1_zfmisc_1 @ 
% 0.10/0.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf(t24_compts_1, axiom,
% 0.10/0.39    (![A:$i]:
% 0.10/0.39     ( ( l1_pre_topc @ A ) =>
% 0.10/0.39       ( ![B:$i]:
% 0.10/0.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.10/0.39           ( ![C:$i]:
% 0.10/0.39             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_pre_topc @ C ) ) =>
% 0.10/0.39               ( ![D:$i]:
% 0.10/0.39                 ( ( ( v1_funct_1 @ D ) & 
% 0.10/0.39                     ( v1_funct_2 @
% 0.10/0.39                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.10/0.39                     ( m1_subset_1 @
% 0.10/0.39                       D @ 
% 0.10/0.39                       ( k1_zfmisc_1 @
% 0.10/0.39                         ( k2_zfmisc_1 @
% 0.10/0.39                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.10/0.39                   ( ( ( v5_pre_topc @ D @ A @ C ) & 
% 0.10/0.39                       ( ( k2_relset_1 @
% 0.10/0.39                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D ) =
% 0.10/0.39                         ( k2_struct_0 @ C ) ) & 
% 0.10/0.39                       ( v2_compts_1 @ B @ A ) ) =>
% 0.10/0.39                     ( v2_compts_1 @
% 0.10/0.39                       ( k7_relset_1 @
% 0.10/0.39                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ 
% 0.10/0.39                       C ) ) ) ) ) ) ) ) ))).
% 0.10/0.39  thf('3', plain,
% 0.10/0.39      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.10/0.39         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.10/0.39          | ~ (v1_funct_1 @ X19)
% 0.10/0.39          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 0.10/0.39          | ~ (m1_subset_1 @ X19 @ 
% 0.10/0.39               (k1_zfmisc_1 @ 
% 0.10/0.39                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))))
% 0.10/0.39          | (v2_compts_1 @ 
% 0.10/0.39             (k7_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20) @ X19 @ 
% 0.10/0.39              X17) @ 
% 0.10/0.39             X20)
% 0.10/0.39          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20) @ X19)
% 0.10/0.39              != (k2_struct_0 @ X20))
% 0.10/0.39          | ~ (v5_pre_topc @ X19 @ X18 @ X20)
% 0.10/0.39          | ~ (v2_compts_1 @ X17 @ X18)
% 0.10/0.39          | ~ (l1_pre_topc @ X20)
% 0.10/0.39          | (v2_struct_0 @ X20)
% 0.10/0.39          | ~ (l1_pre_topc @ X18))),
% 0.10/0.39      inference('cnf', [status(esa)], [t24_compts_1])).
% 0.10/0.39  thf('4', plain,
% 0.10/0.39      (![X0 : $i]:
% 0.10/0.39         (~ (l1_pre_topc @ sk_A)
% 0.10/0.39          | (v2_struct_0 @ sk_B)
% 0.10/0.39          | ~ (l1_pre_topc @ sk_B)
% 0.10/0.39          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.10/0.39          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.10/0.39          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.10/0.39              != (k2_struct_0 @ sk_B))
% 0.10/0.39          | (v2_compts_1 @ 
% 0.10/0.39             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.10/0.39              sk_C @ X0) @ 
% 0.10/0.39             sk_B)
% 0.10/0.39          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.10/0.39          | ~ (v1_funct_1 @ sk_C)
% 0.10/0.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.10/0.39      inference('sup-', [status(thm)], ['2', '3'])).
% 0.10/0.39  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('7', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('8', plain,
% 0.10/0.39      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.10/0.39         = (k2_struct_0 @ sk_B))),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('9', plain,
% 0.10/0.39      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.10/0.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.39  thf('11', plain,
% 0.10/0.39      (![X0 : $i]:
% 0.10/0.39         ((v2_struct_0 @ sk_B)
% 0.10/0.39          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.10/0.39          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.10/0.39          | (v2_compts_1 @ 
% 0.10/0.39             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.10/0.39              sk_C @ X0) @ 
% 0.10/0.39             sk_B)
% 0.10/0.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.10/0.40      inference('demod', [status(thm)], ['4', '5', '6', '7', '8', '9', '10'])).
% 0.10/0.40  thf('12', plain,
% 0.10/0.40      (![X0 : $i]:
% 0.10/0.40         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.10/0.40          | (v2_compts_1 @ 
% 0.10/0.40             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.10/0.40              sk_C @ X0) @ 
% 0.10/0.40             sk_B)
% 0.10/0.40          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.10/0.40          | (v2_struct_0 @ sk_B))),
% 0.10/0.40      inference('simplify', [status(thm)], ['11'])).
% 0.10/0.40  thf('13', plain,
% 0.10/0.40      (((v2_struct_0 @ sk_B)
% 0.10/0.40        | ~ (v2_compts_1 @ sk_D @ sk_A)
% 0.10/0.40        | (v2_compts_1 @ 
% 0.10/0.40           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.10/0.40            sk_D) @ 
% 0.10/0.40           sk_B))),
% 0.10/0.40      inference('sup-', [status(thm)], ['1', '12'])).
% 0.10/0.40  thf(t10_compts_1, axiom,
% 0.10/0.40    (![A:$i]:
% 0.10/0.40     ( ( l1_pre_topc @ A ) =>
% 0.10/0.40       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.10/0.40  thf('14', plain,
% 0.10/0.40      (![X11 : $i]:
% 0.10/0.40         (~ (v1_compts_1 @ X11)
% 0.10/0.40          | (v2_compts_1 @ (k2_struct_0 @ X11) @ X11)
% 0.10/0.40          | ~ (l1_pre_topc @ X11))),
% 0.10/0.40      inference('cnf', [status(esa)], [t10_compts_1])).
% 0.10/0.40  thf(d3_struct_0, axiom,
% 0.10/0.40    (![A:$i]:
% 0.10/0.40     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.10/0.40  thf('15', plain,
% 0.10/0.40      (![X9 : $i]:
% 0.10/0.40         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.10/0.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.10/0.40  thf('16', plain,
% 0.10/0.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf(dt_k2_subset_1, axiom,
% 0.10/0.40    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.10/0.40  thf('17', plain,
% 0.10/0.40      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.10/0.40      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.10/0.40  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.10/0.40  thf('18', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.10/0.40      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.10/0.40  thf('19', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.10/0.40      inference('demod', [status(thm)], ['17', '18'])).
% 0.10/0.40  thf(t18_compts_1, axiom,
% 0.10/0.40    (![A:$i]:
% 0.10/0.40     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.10/0.40       ( ![B:$i]:
% 0.10/0.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.10/0.40           ( ![C:$i]:
% 0.10/0.40             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.10/0.40               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.10/0.40                   ( v4_pre_topc @ C @ A ) ) =>
% 0.10/0.40                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.10/0.40  thf('20', plain,
% 0.10/0.40      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.10/0.40         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.10/0.40          | ~ (v2_compts_1 @ X14 @ X15)
% 0.10/0.40          | ~ (r1_tarski @ X16 @ X14)
% 0.10/0.40          | ~ (v4_pre_topc @ X16 @ X15)
% 0.10/0.40          | (v2_compts_1 @ X16 @ X15)
% 0.10/0.40          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.10/0.40          | ~ (l1_pre_topc @ X15)
% 0.10/0.40          | ~ (v2_pre_topc @ X15))),
% 0.10/0.40      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.10/0.40  thf('21', plain,
% 0.10/0.40      (![X0 : $i, X1 : $i]:
% 0.10/0.40         (~ (v2_pre_topc @ X0)
% 0.10/0.40          | ~ (l1_pre_topc @ X0)
% 0.10/0.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.10/0.40          | (v2_compts_1 @ X1 @ X0)
% 0.10/0.40          | ~ (v4_pre_topc @ X1 @ X0)
% 0.10/0.40          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.10/0.40          | ~ (v2_compts_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.10/0.40      inference('sup-', [status(thm)], ['19', '20'])).
% 0.10/0.40  thf('22', plain,
% 0.10/0.40      ((~ (v2_compts_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.10/0.40        | ~ (r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))
% 0.10/0.40        | ~ (v4_pre_topc @ sk_D @ sk_A)
% 0.10/0.40        | (v2_compts_1 @ sk_D @ sk_A)
% 0.10/0.40        | ~ (l1_pre_topc @ sk_A)
% 0.10/0.40        | ~ (v2_pre_topc @ sk_A))),
% 0.10/0.40      inference('sup-', [status(thm)], ['16', '21'])).
% 0.10/0.40  thf('23', plain,
% 0.10/0.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf(t3_subset, axiom,
% 0.10/0.40    (![A:$i,B:$i]:
% 0.10/0.40     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.10/0.40  thf('24', plain,
% 0.10/0.40      (![X2 : $i, X3 : $i]:
% 0.10/0.40         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.10/0.40      inference('cnf', [status(esa)], [t3_subset])).
% 0.10/0.40  thf('25', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.10/0.40      inference('sup-', [status(thm)], ['23', '24'])).
% 0.10/0.40  thf('26', plain, ((v4_pre_topc @ sk_D @ sk_A)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('29', plain,
% 0.10/0.40      ((~ (v2_compts_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.10/0.40        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.10/0.40      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 0.10/0.40  thf('30', plain,
% 0.10/0.40      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.10/0.40        | ~ (l1_struct_0 @ sk_A)
% 0.10/0.40        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.10/0.40      inference('sup-', [status(thm)], ['15', '29'])).
% 0.10/0.40  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf(dt_l1_pre_topc, axiom,
% 0.10/0.40    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.10/0.40  thf('32', plain,
% 0.10/0.40      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.10/0.40      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.10/0.40  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.10/0.40      inference('sup-', [status(thm)], ['31', '32'])).
% 0.10/0.40  thf('34', plain,
% 0.10/0.40      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.10/0.40        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.10/0.40      inference('demod', [status(thm)], ['30', '33'])).
% 0.10/0.40  thf('35', plain,
% 0.10/0.40      ((~ (l1_pre_topc @ sk_A)
% 0.10/0.40        | ~ (v1_compts_1 @ sk_A)
% 0.10/0.40        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.10/0.40      inference('sup-', [status(thm)], ['14', '34'])).
% 0.10/0.40  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('37', plain, ((v1_compts_1 @ sk_A)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('38', plain, ((v2_compts_1 @ sk_D @ sk_A)),
% 0.10/0.40      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.10/0.40  thf('39', plain,
% 0.10/0.40      (((v2_struct_0 @ sk_B)
% 0.10/0.40        | (v2_compts_1 @ 
% 0.10/0.40           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.10/0.40            sk_D) @ 
% 0.10/0.40           sk_B))),
% 0.10/0.40      inference('demod', [status(thm)], ['13', '38'])).
% 0.10/0.40  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('41', plain,
% 0.10/0.40      ((v2_compts_1 @ 
% 0.10/0.40        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.10/0.40         sk_D) @ 
% 0.10/0.40        sk_B)),
% 0.10/0.40      inference('clc', [status(thm)], ['39', '40'])).
% 0.10/0.40  thf('42', plain,
% 0.10/0.40      ((m1_subset_1 @ sk_C @ 
% 0.10/0.40        (k1_zfmisc_1 @ 
% 0.10/0.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf(dt_k7_relset_1, axiom,
% 0.10/0.40    (![A:$i,B:$i,C:$i,D:$i]:
% 0.10/0.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.10/0.40       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.10/0.40  thf('43', plain,
% 0.10/0.40      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.10/0.40         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.10/0.40          | (m1_subset_1 @ (k7_relset_1 @ X6 @ X7 @ X5 @ X8) @ 
% 0.10/0.40             (k1_zfmisc_1 @ X7)))),
% 0.10/0.40      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.10/0.40  thf('44', plain,
% 0.10/0.40      (![X0 : $i]:
% 0.10/0.40         (m1_subset_1 @ 
% 0.10/0.40          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.10/0.40           X0) @ 
% 0.10/0.40          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.10/0.40      inference('sup-', [status(thm)], ['42', '43'])).
% 0.10/0.40  thf(t16_compts_1, axiom,
% 0.10/0.40    (![A:$i]:
% 0.10/0.40     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.10/0.40       ( ![B:$i]:
% 0.10/0.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.10/0.40           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.10/0.40             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.10/0.40  thf('45', plain,
% 0.10/0.40      (![X12 : $i, X13 : $i]:
% 0.10/0.40         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.10/0.40          | (v4_pre_topc @ X12 @ X13)
% 0.10/0.40          | ~ (v2_compts_1 @ X12 @ X13)
% 0.10/0.40          | ~ (v8_pre_topc @ X13)
% 0.10/0.40          | ~ (l1_pre_topc @ X13)
% 0.10/0.40          | ~ (v2_pre_topc @ X13))),
% 0.10/0.40      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.10/0.40  thf('46', plain,
% 0.10/0.40      (![X0 : $i]:
% 0.10/0.40         (~ (v2_pre_topc @ sk_B)
% 0.10/0.40          | ~ (l1_pre_topc @ sk_B)
% 0.10/0.40          | ~ (v8_pre_topc @ sk_B)
% 0.10/0.40          | ~ (v2_compts_1 @ 
% 0.10/0.40               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.10/0.40                sk_C @ X0) @ 
% 0.10/0.40               sk_B)
% 0.10/0.40          | (v4_pre_topc @ 
% 0.10/0.40             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.10/0.40              sk_C @ X0) @ 
% 0.10/0.40             sk_B))),
% 0.10/0.40      inference('sup-', [status(thm)], ['44', '45'])).
% 0.10/0.40  thf('47', plain, ((v2_pre_topc @ sk_B)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('49', plain, ((v8_pre_topc @ sk_B)),
% 0.10/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.10/0.40  thf('50', plain,
% 0.10/0.40      (![X0 : $i]:
% 0.10/0.40         (~ (v2_compts_1 @ 
% 0.10/0.40             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.10/0.40              sk_C @ X0) @ 
% 0.10/0.40             sk_B)
% 0.10/0.40          | (v4_pre_topc @ 
% 0.10/0.40             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.10/0.40              sk_C @ X0) @ 
% 0.10/0.40             sk_B))),
% 0.10/0.40      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.10/0.40  thf('51', plain,
% 0.10/0.40      ((v4_pre_topc @ 
% 0.10/0.40        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.10/0.40         sk_D) @ 
% 0.10/0.40        sk_B)),
% 0.10/0.40      inference('sup-', [status(thm)], ['41', '50'])).
% 0.10/0.40  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.10/0.40  
% 0.10/0.40  % SZS output end Refutation
% 0.10/0.40  
% 0.10/0.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
