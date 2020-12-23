%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IakVN9KULc

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 200 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   29
%              Number of atoms          : 1142 (2762 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(o_2_4_waybel_9_type,type,(
    o_2_4_waybel_9: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t8_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_9])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_o_2_4_waybel_9,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( o_2_4_waybel_9 @ A @ B ) @ ( u1_struct_0 @ B ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( m1_subset_1 @ ( o_2_4_waybel_9 @ X19 @ X20 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_4_waybel_9])).

thf('5',plain,
    ( ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ? [D: $i] :
                  ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( r1_orders_2 @ B @ D @ E )
                       => ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) )
                  & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( r1_waybel_0 @ X7 @ X6 @ X9 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_waybel_0 @ X0 @ sk_B @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( ( k2_waybel_0 @ X13 @ X12 @ X14 )
        = ( k3_funct_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_waybel_0 @ X13 @ X12 ) @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_waybel_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t189_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ( r2_hidden @ ( k3_funct_2 @ X2 @ X0 @ X1 @ X3 ) @ ( k2_relset_1 @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t189_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( v1_funct_2 @ ( u1_waybel_0 @ X17 @ X18 ) @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('34',plain,
    ( ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('39',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B @ ( sk_E @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_B @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X7 @ X6 @ ( sk_E @ X8 @ X9 @ X6 @ X7 ) ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( r1_waybel_0 @ X7 @ X6 @ X9 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( o_2_4_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('50',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_0 @ sk_A @ sk_B @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','67'])).

thf('69',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( l1_orders_2 @ X15 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('71',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IakVN9KULc
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 44 iterations in 0.037s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.49  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(o_2_4_waybel_9_type, type, o_2_4_waybel_9: $i > $i > $i).
% 0.20/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(dt_l1_orders_2, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('0', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.49  thf(t8_waybel_9, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( r1_waybel_0 @
% 0.20/0.49             A @ B @ 
% 0.20/0.49             ( k2_relset_1 @
% 0.20/0.49               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.49               ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49              ( r1_waybel_0 @
% 0.20/0.49                A @ B @ 
% 0.20/0.49                ( k2_relset_1 @
% 0.20/0.49                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.49                  ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t8_waybel_9])).
% 0.20/0.49  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_o_2_4_waybel_9, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.49         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( o_2_4_waybel_9 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X19)
% 0.20/0.49          | (v2_struct_0 @ X19)
% 0.20/0.49          | (v2_struct_0 @ X20)
% 0.20/0.49          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.20/0.49          | (m1_subset_1 @ (o_2_4_waybel_9 @ X19 @ X20) @ (u1_struct_0 @ X20)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_o_2_4_waybel_9])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(d11_waybel_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.49               ( ?[D:$i]:
% 0.20/0.49                 ( ( ![E:$i]:
% 0.20/0.49                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.20/0.49                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.20/0.49                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X6)
% 0.20/0.49          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.20/0.49          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X6 @ X7) @ (u1_struct_0 @ X6))
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.20/0.49          | (r1_waybel_0 @ X7 @ X6 @ X9)
% 0.20/0.49          | ~ (l1_struct_0 @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_struct_0 @ X0)
% 0.20/0.49          | (r1_waybel_0 @ X0 @ sk_B @ X1)
% 0.20/0.49          | (m1_subset_1 @ 
% 0.20/0.49             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X1 @ sk_B @ X0) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | (m1_subset_1 @ 
% 0.20/0.49             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '13'])).
% 0.20/0.49  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | (m1_subset_1 @ 
% 0.20/0.49             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf(d8_waybel_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49               ( ( k2_waybel_0 @ A @ B @ C ) =
% 0.20/0.49                 ( k3_funct_2 @
% 0.20/0.49                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.49                   ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X12)
% 0.20/0.49          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.20/0.49          | ((k2_waybel_0 @ X13 @ X12 @ X14)
% 0.20/0.49              = (k3_funct_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.20/0.49                 (u1_waybel_0 @ X13 @ X12) @ X14))
% 0.20/0.49          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (l1_struct_0 @ X13)
% 0.20/0.49          | (v2_struct_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_waybel_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ X1)
% 0.20/0.49          | ~ (l1_struct_0 @ X1)
% 0.20/0.49          | ((k2_waybel_0 @ X1 @ sk_B @ 
% 0.20/0.49              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A))
% 0.20/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X1) @ 
% 0.20/0.49                 (u1_waybel_0 @ X1 @ sk_B) @ 
% 0.20/0.49                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)))
% 0.20/0.49          | ~ (l1_waybel_0 @ sk_B @ X1)
% 0.20/0.49          | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (l1_waybel_0 @ sk_B @ X1)
% 0.20/0.49          | ((k2_waybel_0 @ X1 @ sk_B @ 
% 0.20/0.49              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A))
% 0.20/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X1) @ 
% 0.20/0.49                 (u1_waybel_0 @ X1 @ sk_B) @ 
% 0.20/0.49                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)))
% 0.20/0.49          | ~ (l1_struct_0 @ X1)
% 0.20/0.49          | (v2_struct_0 @ X1)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49          | ((k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A))
% 0.20/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49                 (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.49                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '19'])).
% 0.20/0.49  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ((k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A))
% 0.20/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49                 (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.49                 (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49            (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A))
% 0.20/0.49            = (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49               (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.49               (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)))
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_B)
% 0.20/0.49          | (m1_subset_1 @ 
% 0.20/0.49             (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('25', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_u1_waybel_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.20/0.49         ( v1_funct_2 @
% 0.20/0.49           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.49         ( m1_subset_1 @
% 0.20/0.49           ( u1_waybel_0 @ A @ B ) @ 
% 0.20/0.49           ( k1_zfmisc_1 @
% 0.20/0.49             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X17)
% 0.20/0.49          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.49          | (m1_subset_1 @ (u1_waybel_0 @ X17 @ X18) @ 
% 0.20/0.49             (k1_zfmisc_1 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17)))))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.49         (k1_zfmisc_1 @ 
% 0.20/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ 
% 0.20/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf(t189_funct_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.49                     ( m1_subset_1 @
% 0.20/0.49                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49                   ( r2_hidden @
% 0.20/0.49                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.20/0.49                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.20/0.49          | (r2_hidden @ (k3_funct_2 @ X2 @ X0 @ X1 @ X3) @ 
% 0.20/0.49             (k2_relset_1 @ X2 @ X0 @ X1))
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ X2)
% 0.20/0.49          | (v1_xboole_0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t189_funct_2])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_waybel_0 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49          | ~ (v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.49               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B))
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X17)
% 0.20/0.49          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.49          | (v1_funct_2 @ (u1_waybel_0 @ X17 @ X18) @ (u1_struct_0 @ X18) @ 
% 0.20/0.49             (u1_struct_0 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49         (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X17)
% 0.20/0.49          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.49          | (v1_funct_1 @ (u1_waybel_0 @ X17 @ X18)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_waybel_0 @ sk_A @ sk_B) @ X0) @ 
% 0.20/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '36', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.49              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ 
% 0.20/0.49           (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49            (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['23', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_waybel_0 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k2_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49              (sk_E @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_B @ sk_A)) @ 
% 0.20/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49              (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X6)
% 0.20/0.49          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ 
% 0.20/0.49               (k2_waybel_0 @ X7 @ X6 @ (sk_E @ X8 @ X9 @ X6 @ X7)) @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.20/0.49          | (r1_waybel_0 @ X7 @ X6 @ X9)
% 0.20/0.49          | ~ (l1_struct_0 @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49        | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49        | ~ (m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B))
% 0.20/0.49        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((m1_subset_1 @ (o_2_4_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('50', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49        | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (~ (r1_waybel_0 @ sk_A @ sk_B @ 
% 0.20/0.49          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.49           (u1_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf(fc2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (![X4 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.20/0.49          | ~ (l1_struct_0 @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.49  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('63', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (![X4 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.20/0.49          | ~ (l1_struct_0 @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('65', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('67', plain, (~ (l1_struct_0 @ sk_B)),
% 0.20/0.49      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.49  thf('68', plain, (~ (l1_orders_2 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '67'])).
% 0.20/0.49  thf('69', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_waybel_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) =>
% 0.20/0.49       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (l1_waybel_0 @ X15 @ X16)
% 0.20/0.49          | (l1_orders_2 @ X15)
% 0.20/0.49          | ~ (l1_struct_0 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.49  thf('71', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('73', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.49  thf('74', plain, ($false), inference('demod', [status(thm)], ['68', '73'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
