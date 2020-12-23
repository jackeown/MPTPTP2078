%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1662+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fSbENu0gI4

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:57 EST 2020

% Result     : Theorem 24.73s
% Output     : Refutation 24.73s
% Verified   : 
% Statistics : Number of formulae       :  256 ( 682 expanded)
%              Number of leaves         :   58 ( 217 expanded)
%              Depth                    :   28
%              Number of atoms          : 2695 (12307 expanded)
%              Number of equality atoms :   53 ( 276 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(t42_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( ( v1_finset_1 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) )
               => ( ( C != k1_xboole_0 )
                 => ( r2_hidden @ ( k1_yellow_0 @ A @ C ) @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v12_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_waybel_0 @ B @ A )
            <=> ! [C: $i] :
                  ( ( ( v1_finset_1 @ C )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) )
                 => ( ( C != k1_xboole_0 )
                   => ( r2_hidden @ ( k1_yellow_0 @ A @ C ) @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_waybel_0])).

thf('0',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v1_finset_1 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_finset_1 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('9',plain,
    ( ( v1_finset_1 @ sk_C_2 )
   <= ( v1_finset_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('14',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_2 )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_2 @ X0 )
        | ~ ( r1_tarski @ sk_B_2 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t54_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v1_lattice3 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_finset_1 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( r1_yellow_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_lattice3 @ X46 )
      | ( r1_yellow_0 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v1_finset_1 @ X47 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 )
      | ~ ( v4_orders_2 @ X46 )
      | ~ ( v3_orders_2 @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t54_yellow_0])).

thf('22',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_finset_1 @ sk_C_2 )
      | ( r1_yellow_0 @ sk_A @ sk_C_2 )
      | ~ ( v1_lattice3 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_finset_1 @ sk_C_2 )
      | ( r1_yellow_0 @ sk_A @ sk_C_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('29',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C_2 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('32',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( r1_yellow_0 @ sk_A @ sk_C_2 ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X51: $i] :
      ( ~ ( v1_finset_1 @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 )
      | ( X51 = k1_xboole_0 )
      | ( v1_waybel_0 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf(t1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_waybel_0 @ B @ A )
              & ~ ( v1_xboole_0 @ B ) )
          <=> ! [C: $i] :
                ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
                  & ( v1_finset_1 @ C ) )
               => ? [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                    & ( r2_hidden @ D @ B )
                    & ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_0 @ B @ A )
    <=> ( ~ ( v1_xboole_0 @ B )
        & ( v1_waybel_0 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X8 @ X10 )
      | ~ ( v1_waybel_0 @ X8 @ X10 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) )
   <= ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( ( v1_finset_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) )
       => ? [D: $i] :
            ( ( r2_lattice3 @ A @ C @ D )
            & ( r2_hidden @ D @ B )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( zip_tseitin_0 @ B @ A )
          <=> ! [C: $i] :
                ( zip_tseitin_1 @ C @ B @ A ) ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( ( v1_finset_1 @ sk_C_2 )
   <= ( v1_finset_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( r2_lattice3 @ X13 @ X11 @ ( sk_D_1 @ X13 @ X12 @ X11 ) )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ X0 )
        | ( r2_lattice3 @ X0 @ sk_C_2 @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_C_2 ) )
        | ~ ( v1_finset_1 @ sk_C_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ X0 @ sk_C_2 @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_C_2 ) )
        | ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_2 @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('58',plain,
    ( ( v1_finset_1 @ sk_C_2 )
   <= ( v1_finset_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X13 @ X12 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ X0 )
        | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_C_2 ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_finset_1 @ sk_C_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_C_2 ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(t30_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) )
               => ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_4: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_4 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_2 @ D @ C @ B @ A ) )
     => ( zip_tseitin_3 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_3 @ D @ C @ B @ A ) )
               => ( zip_tseitin_4 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( X35
       != ( k1_yellow_0 @ X36 @ X37 ) )
      | ~ ( r1_yellow_0 @ X36 @ X37 )
      | ~ ( r2_lattice3 @ X36 @ X37 @ X38 )
      | ( r1_orders_2 @ X36 @ X35 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('66',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v5_orders_2 @ X36 )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ( r1_orders_2 @ X36 @ ( k1_yellow_0 @ X36 @ X37 ) @ X38 )
      | ~ ( r2_lattice3 @ X36 @ X37 @ X38 )
      | ~ ( r1_yellow_0 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X36 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_yellow_0 @ sk_A @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
        | ~ ( v5_orders_2 @ sk_A ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_yellow_0 @ sk_A @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['56','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['35','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v12_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ D @ C ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v12_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r2_hidden @ X3 @ X1 )
      | ~ ( r1_orders_2 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v12_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) )
        | ~ ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ sk_B_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('84',plain,
    ( ( v1_finset_1 @ sk_C_2 )
   <= ( v1_finset_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('86',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_finset_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X12 @ X11 ) @ X12 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_C_2 ) @ sk_B_2 )
        | ~ ( v1_finset_1 @ sk_C_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_C_2 ) @ sk_B_2 )
        | ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) @ sk_B_2 )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['74','90'])).

thf('92',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','91'])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
   <= ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
   <= ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      & ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('97',plain,(
    ! [X48: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('98',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      & ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 )
      & ( sk_C_2 != k1_xboole_0 )
      & ( v1_waybel_0 @ sk_B_2 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_finset_1 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_B_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) )
    | ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('103',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X11 @ X12 @ X14 )
      | ( v1_finset_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('104',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( zip_tseitin_1 @ ( sk_C_1 @ X16 @ X17 ) @ X16 @ X17 )
      | ( zip_tseitin_0 @ X16 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v1_finset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('114',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X11 @ X12 @ X14 )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('115',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 @ X2 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('118',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( r1_tarski @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','120'])).

thf('122',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('123',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_lattice3 @ X46 )
      | ( r1_yellow_0 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v1_finset_1 @ X47 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 )
      | ~ ( v4_orders_2 @ X46 )
      | ~ ( v3_orders_2 @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t54_yellow_0])).

thf('125',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_finset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_finset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('132',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('135',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( X35
       != ( k1_yellow_0 @ X36 @ X37 ) )
      | ~ ( r1_yellow_0 @ X36 @ X37 )
      | ( r2_lattice3 @ X36 @ X37 @ X35 )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('136',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v5_orders_2 @ X36 )
      | ~ ( l1_orders_2 @ X36 )
      | ( r2_lattice3 @ X36 @ X37 @ ( k1_yellow_0 @ X36 @ X37 ) )
      | ~ ( r1_yellow_0 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X36 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v5_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( v1_finset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('144',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('145',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('146',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['36'])).

thf('148',plain,
    ( ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_B_2 )
      | ~ ( v1_finset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_B_2 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_B_2 )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('152',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X11 @ X12 @ X14 )
      | ~ ( r2_lattice3 @ X14 @ X11 @ X15 )
      | ~ ( r2_hidden @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( zip_tseitin_1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
        | ( ( sk_C_1 @ sk_B_2 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
        | ( ( sk_C_1 @ sk_B_2 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ sk_B_2 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['142','156'])).

thf('158',plain,
    ( ( ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X48: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('166',plain,
    ( ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( ( sk_C_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('168',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('169',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('170',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('173',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('174',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( m1_subset_1 @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('179',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X50 ) )
      | ( r2_lattice3 @ X50 @ k1_xboole_0 @ X49 )
      | ~ ( l1_orders_2 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('180',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_B @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_B @ sk_B_2 ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('184',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X11 @ X12 @ X14 )
      | ~ ( r2_lattice3 @ X14 @ X11 @ X15 )
      | ~ ( r2_hidden @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ sk_B_2 ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_B @ sk_B_2 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['171','186'])).

thf('188',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A ) )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['168','189'])).

thf('191',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_waybel_0 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('193',plain,
    ( ( v1_waybel_0 @ sk_B_2 @ sk_A )
   <= ! [X51: $i] :
        ( ( X51 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X51 )
        | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ~ ( v1_waybel_0 @ sk_B_2 @ sk_A )
   <= ~ ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('195',plain,
    ( ~ ! [X51: $i] :
          ( ( X51 = k1_xboole_0 )
          | ~ ( v1_finset_1 @ X51 )
          | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ sk_B_2 ) )
          | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X51 ) @ sk_B_2 ) )
    | ( v1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','101','102','195'])).


%------------------------------------------------------------------------------
