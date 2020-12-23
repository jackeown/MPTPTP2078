%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GzhJ3kALxu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:41 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 131 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  769 (3296 expanded)
%              Number of equality atoms :   11 (  53 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) @ X20 @ X18 ) @ X21 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) @ X20 )
       != ( k2_struct_0 @ X21 ) )
      | ~ ( v5_pre_topc @ X20 @ X19 @ X21 )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X12: $i] :
      ( ~ ( v1_compts_1 @ X12 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_compts_1 @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( v4_pre_topc @ X17 @ X16 )
      | ( v2_compts_1 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ X0 )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v2_compts_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_D @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v4_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v2_compts_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['23','26','27','28','29'])).

thf('31',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['14','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_compts_1 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( v2_compts_1 @ X13 @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GzhJ3kALxu
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:00:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 202 iterations in 0.124s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.59  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.39/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.39/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.39/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.59  thf(t25_compts_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59             ( l1_pre_topc @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                 ( m1_subset_1 @
% 0.39/0.59                   C @ 
% 0.39/0.59                   ( k1_zfmisc_1 @
% 0.39/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.39/0.59                   ( ( k2_relset_1 @
% 0.39/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.59                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.39/0.59                 ( ![D:$i]:
% 0.39/0.59                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59                     ( ( v4_pre_topc @ D @ A ) =>
% 0.39/0.59                       ( v4_pre_topc @
% 0.39/0.59                         ( k7_relset_1 @
% 0.39/0.59                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.39/0.59                         B ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59                ( l1_pre_topc @ B ) ) =>
% 0.39/0.59              ( ![C:$i]:
% 0.39/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.59                    ( v1_funct_2 @
% 0.39/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                    ( m1_subset_1 @
% 0.39/0.59                      C @ 
% 0.39/0.59                      ( k1_zfmisc_1 @
% 0.39/0.59                        ( k2_zfmisc_1 @
% 0.39/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.39/0.59                      ( ( k2_relset_1 @
% 0.39/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.59                        ( k2_struct_0 @ B ) ) & 
% 0.39/0.59                      ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.39/0.59                    ( ![D:$i]:
% 0.39/0.59                      ( ( m1_subset_1 @
% 0.39/0.59                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59                        ( ( v4_pre_topc @ D @ A ) =>
% 0.39/0.59                          ( v4_pre_topc @
% 0.39/0.59                            ( k7_relset_1 @
% 0.39/0.59                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.39/0.59                            B ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t25_compts_1])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (~ (v4_pre_topc @ 
% 0.39/0.59          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59           sk_D) @ 
% 0.39/0.59          sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t24_compts_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_pre_topc @ C ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( ( v1_funct_1 @ D ) & 
% 0.39/0.59                     ( v1_funct_2 @
% 0.39/0.59                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.39/0.59                     ( m1_subset_1 @
% 0.39/0.59                       D @ 
% 0.39/0.59                       ( k1_zfmisc_1 @
% 0.39/0.59                         ( k2_zfmisc_1 @
% 0.39/0.59                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.39/0.59                   ( ( ( v5_pre_topc @ D @ A @ C ) & 
% 0.39/0.59                       ( ( k2_relset_1 @
% 0.39/0.59                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D ) =
% 0.39/0.59                         ( k2_struct_0 @ C ) ) & 
% 0.39/0.59                       ( v2_compts_1 @ B @ A ) ) =>
% 0.39/0.59                     ( v2_compts_1 @
% 0.39/0.59                       ( k7_relset_1 @
% 0.39/0.59                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ 
% 0.39/0.59                       C ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.59          | ~ (v1_funct_1 @ X20)
% 0.39/0.59          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))
% 0.39/0.59          | ~ (m1_subset_1 @ X20 @ 
% 0.39/0.59               (k1_zfmisc_1 @ 
% 0.39/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))))
% 0.39/0.59          | (v2_compts_1 @ 
% 0.39/0.59             (k7_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21) @ X20 @ 
% 0.39/0.59              X18) @ 
% 0.39/0.59             X21)
% 0.39/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21) @ X20)
% 0.39/0.59              != (k2_struct_0 @ X21))
% 0.39/0.59          | ~ (v5_pre_topc @ X20 @ X19 @ X21)
% 0.39/0.59          | ~ (v2_compts_1 @ X18 @ X19)
% 0.39/0.59          | ~ (l1_pre_topc @ X21)
% 0.39/0.59          | (v2_struct_0 @ X21)
% 0.39/0.59          | ~ (l1_pre_topc @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [t24_compts_1])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B)
% 0.39/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.59          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.39/0.59          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.39/0.59          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59              != (k2_struct_0 @ sk_B))
% 0.39/0.59          | (v2_compts_1 @ 
% 0.39/0.59             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59              sk_C @ X0) @ 
% 0.39/0.59             sk_B)
% 0.39/0.59          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('7', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B)
% 0.39/0.59          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.39/0.59          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.59          | (v2_compts_1 @ 
% 0.39/0.59             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59              sk_C @ X0) @ 
% 0.39/0.59             sk_B)
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['4', '5', '6', '7', '8', '9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59          | (v2_compts_1 @ 
% 0.39/0.59             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59              sk_C @ X0) @ 
% 0.39/0.59             sk_B)
% 0.39/0.59          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_B)
% 0.39/0.59        | ~ (v2_compts_1 @ sk_D @ sk_A)
% 0.39/0.59        | (v2_compts_1 @ 
% 0.39/0.59           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59            sk_D) @ 
% 0.39/0.59           sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '12'])).
% 0.39/0.59  thf(t10_compts_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X12 : $i]:
% 0.39/0.59         (~ (v1_compts_1 @ X12)
% 0.39/0.59          | (v2_compts_1 @ (k2_struct_0 @ X12) @ X12)
% 0.39/0.59          | ~ (l1_pre_topc @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t10_compts_1])).
% 0.39/0.59  thf(d3_struct_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X10 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d10_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('18', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.59  thf(t3_subset, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X3 : $i, X5 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('20', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf(t18_compts_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.39/0.59                   ( v4_pre_topc @ C @ A ) ) =>
% 0.39/0.59                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.59          | ~ (v2_compts_1 @ X15 @ X16)
% 0.39/0.59          | ~ (r1_tarski @ X17 @ X15)
% 0.39/0.59          | ~ (v4_pre_topc @ X17 @ X16)
% 0.39/0.59          | (v2_compts_1 @ X17 @ X16)
% 0.39/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.59          | ~ (l1_pre_topc @ X16)
% 0.39/0.59          | ~ (v2_pre_topc @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v2_pre_topc @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0)
% 0.39/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.39/0.59          | (v2_compts_1 @ X1 @ X0)
% 0.39/0.59          | ~ (v4_pre_topc @ X1 @ X0)
% 0.39/0.59          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.39/0.59          | ~ (v2_compts_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      ((~ (v2_compts_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.39/0.59        | ~ (r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | ~ (v4_pre_topc @ sk_D @ sk_A)
% 0.39/0.59        | (v2_compts_1 @ sk_D @ sk_A)
% 0.39/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.59        | ~ (v2_pre_topc @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '22'])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('26', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain, ((v4_pre_topc @ sk_D @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      ((~ (v2_compts_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.39/0.59        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['23', '26', '27', '28', '29'])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.39/0.59        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.59        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['15', '30'])).
% 0.39/0.59  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(dt_l1_pre_topc, axiom,
% 0.39/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.59  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.39/0.59        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['31', '34'])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.59        | ~ (v1_compts_1 @ sk_A)
% 0.39/0.59        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['14', '35'])).
% 0.39/0.59  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('38', plain, ((v1_compts_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('39', plain, ((v2_compts_1 @ sk_D @ sk_A)),
% 0.39/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_B)
% 0.39/0.59        | (v2_compts_1 @ 
% 0.39/0.59           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59            sk_D) @ 
% 0.39/0.59           sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['13', '39'])).
% 0.39/0.59  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      ((v2_compts_1 @ 
% 0.39/0.59        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59         sk_D) @ 
% 0.39/0.59        sk_B)),
% 0.39/0.59      inference('clc', [status(thm)], ['40', '41'])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(dt_k7_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.39/0.59          | (m1_subset_1 @ (k7_relset_1 @ X7 @ X8 @ X6 @ X9) @ 
% 0.39/0.59             (k1_zfmisc_1 @ X8)))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (m1_subset_1 @ 
% 0.39/0.59          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59           X0) @ 
% 0.39/0.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf(t16_compts_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.39/0.59             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.39/0.59          | (v4_pre_topc @ X13 @ X14)
% 0.39/0.59          | ~ (v2_compts_1 @ X13 @ X14)
% 0.39/0.59          | ~ (v8_pre_topc @ X14)
% 0.39/0.59          | ~ (l1_pre_topc @ X14)
% 0.39/0.59          | ~ (v2_pre_topc @ X14))),
% 0.39/0.59      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v2_pre_topc @ sk_B)
% 0.39/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.59          | ~ (v8_pre_topc @ sk_B)
% 0.39/0.59          | ~ (v2_compts_1 @ 
% 0.39/0.59               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59                sk_C @ X0) @ 
% 0.39/0.59               sk_B)
% 0.39/0.59          | (v4_pre_topc @ 
% 0.39/0.59             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59              sk_C @ X0) @ 
% 0.39/0.59             sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.59  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('50', plain, ((v8_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v2_compts_1 @ 
% 0.39/0.59             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59              sk_C @ X0) @ 
% 0.39/0.59             sk_B)
% 0.39/0.59          | (v4_pre_topc @ 
% 0.39/0.59             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59              sk_C @ X0) @ 
% 0.39/0.59             sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      ((v4_pre_topc @ 
% 0.39/0.59        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59         sk_D) @ 
% 0.39/0.59        sk_B)),
% 0.39/0.59      inference('sup-', [status(thm)], ['42', '51'])).
% 0.39/0.59  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
