%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1662+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TwIFvsdcWd

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:57 EST 2020

% Result     : Theorem 41.95s
% Output     : Refutation 41.95s
% Verified   : 
% Statistics : Number of formulae       :  285 (1173 expanded)
%              Number of leaves         :   63 ( 351 expanded)
%              Depth                    :   31
%              Number of atoms          : 2941 (22193 expanded)
%              Number of equality atoms :   54 ( 484 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(o_2_7_waybel_0_type,type,(
    o_2_7_waybel_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
   <= ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
    | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( v1_finset_1 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_finset_1 @ sk_C_2 )
    | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('10',plain,
    ( ( v1_finset_1 @ sk_C_2 )
   <= ( v1_finset_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['7'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('15',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X31 )
      | ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_2 @ X0 )
        | ~ ( r1_tarski @ sk_B_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_lattice3 @ X56 )
      | ( r1_yellow_0 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v1_finset_1 @ X57 )
      | ( v1_xboole_0 @ X57 )
      | ~ ( l1_orders_2 @ X56 )
      | ~ ( v5_orders_2 @ X56 )
      | ~ ( v4_orders_2 @ X56 )
      | ~ ( v3_orders_2 @ X56 )
      | ( v2_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t54_yellow_0])).

thf('23',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_finset_1 @ sk_C_2 )
      | ( r1_yellow_0 @ sk_A @ sk_C_2 )
      | ~ ( v1_lattice3 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_finset_1 @ sk_C_2 )
      | ( r1_yellow_0 @ sk_A @ sk_C_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('30',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_C_2 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('33',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( r1_yellow_0 @ sk_A @ sk_C_2 ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X61: $i] :
      ( ~ ( v1_finset_1 @ X61 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 )
      | ( X61 = k1_xboole_0 )
      | ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

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

thf('39',plain,(
    ! [X18: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X18 @ X20 )
      | ~ ( v1_waybel_0 @ X18 @ X20 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_B_1 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,
    ( ( v1_finset_1 @ sk_C_2 )
   <= ( v1_finset_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['7'])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_finset_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( r2_lattice3 @ X23 @ X21 @ ( sk_D_1 @ X23 @ X22 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ X0 )
        | ( r2_lattice3 @ X0 @ sk_C_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_C_2 ) )
        | ~ ( v1_finset_1 @ sk_C_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ X0 @ sk_C_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_C_2 ) )
        | ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_2 @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_B_1 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('59',plain,
    ( ( v1_finset_1 @ sk_C_2 )
   <= ( v1_finset_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['7'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('61',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_finset_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( r2_hidden @ ( sk_D_1 @ X23 @ X22 @ X21 ) @ X22 )
      | ~ ( zip_tseitin_1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
        | ~ ( v1_finset_1 @ sk_C_2 ) )
   <= ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
        | ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('66',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) )
      | ( m1_subset_1 @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X46 ) )
      | ( X45
       != ( k1_yellow_0 @ X46 @ X47 ) )
      | ~ ( r1_yellow_0 @ X46 @ X47 )
      | ~ ( r2_lattice3 @ X46 @ X47 @ X48 )
      | ( r1_orders_2 @ X46 @ X45 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X46 ) )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('71',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v5_orders_2 @ X46 )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X46 ) )
      | ( r1_orders_2 @ X46 @ ( k1_yellow_0 @ X46 @ X47 ) @ X48 )
      | ~ ( r2_lattice3 @ X46 @ X47 @ X48 )
      | ~ ( r1_yellow_0 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X46 @ X47 ) @ ( u1_struct_0 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_yellow_0 @ sk_A @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
        | ~ ( v5_orders_2 @ sk_A ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_yellow_0 @ sk_A @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
        | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['57','77'])).

thf('79',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('82',plain,(
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

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v12_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
        | ~ ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('95',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
   <= ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('96',plain,(
    ! [X58: $i] :
      ( ( X58 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('97',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
      & ( sk_C_2 != k1_xboole_0 )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      & ( v1_finset_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_2 ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','100'])).

thf('102',plain,(
    ~ ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_o_2_7_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( v12_waybel_0 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m2_subset_1 @ ( o_2_7_waybel_0 @ A @ B ) @ ( u1_struct_0 @ A ) @ B ) ) )).

thf('104',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v12_waybel_0 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m2_subset_1 @ ( o_2_7_waybel_0 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_7_waybel_0])).

thf('105',plain,
    ( ( m2_subset_1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v12_waybel_0 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v12_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( m2_subset_1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m2_subset_1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('116',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X17 @ X15 )
      | ~ ( m2_subset_1 @ X17 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( m1_subset_1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('121',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('122',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( r2_hidden @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( r2_hidden @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('128',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( u1_struct_0 @ X60 ) )
      | ( r2_lattice3 @ X60 @ k1_xboole_0 @ X59 )
      | ~ ( l1_orders_2 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('133',plain,(
    ! [X21: $i,X22: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X24 )
      | ~ ( r2_lattice3 @ X24 @ X21 @ X25 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_A )
      | ~ ( r2_hidden @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( o_2_7_waybel_0 @ sk_A @ sk_B_1 ) @ X0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','136'])).

thf('138',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X24 )
      | ( v1_finset_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('140',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( zip_tseitin_1 @ ( sk_C_1 @ X26 @ X27 ) @ X26 @ X27 )
      | ( zip_tseitin_0 @ X26 @ X27 )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('147',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v1_finset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','147'])).

thf('149',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('150',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X24 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('151',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 @ X2 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('154',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X31 )
      | ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','156'])).

thf('158',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('159',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_lattice3 @ X56 )
      | ( r1_yellow_0 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v1_finset_1 @ X57 )
      | ( v1_xboole_0 @ X57 )
      | ~ ( l1_orders_2 @ X56 )
      | ~ ( v5_orders_2 @ X56 )
      | ~ ( v4_orders_2 @ X56 )
      | ~ ( v3_orders_2 @ X56 )
      | ( v2_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t54_yellow_0])).

thf('161',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_finset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_finset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166'])).

thf('168',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','167'])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('171',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ X46 ) )
      | ( X45
       != ( k1_yellow_0 @ X46 @ X47 ) )
      | ~ ( r1_yellow_0 @ X46 @ X47 )
      | ( r2_lattice3 @ X46 @ X47 @ X45 )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('172',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v5_orders_2 @ X46 )
      | ~ ( l1_orders_2 @ X46 )
      | ( r2_lattice3 @ X46 @ X47 @ ( k1_yellow_0 @ X46 @ X47 ) )
      | ~ ( r1_yellow_0 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X46 @ X47 ) @ ( u1_struct_0 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v5_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['169','174'])).

thf('176',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( v1_finset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','147'])).

thf('180',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('181',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('182',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['37'])).

thf('184',plain,
    ( ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ sk_B_1 )
      | ~ ( v1_finset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['179','184'])).

thf('186',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ sk_B_1 )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X5 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('188',plain,(
    ! [X21: $i,X22: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X24 )
      | ~ ( r2_lattice3 @ X24 @ X21 @ X25 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( zip_tseitin_1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
        | ( ( sk_C_1 @ sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ sk_B_1 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
        | ( ( sk_C_1 @ sk_B_1 @ sk_A )
          = k1_xboole_0 )
        | ( zip_tseitin_1 @ X0 @ sk_B_1 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_yellow_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['178','192'])).

thf('194',plain,
    ( ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('196',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X58: $i] :
      ( ( X58 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('199',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('202',plain,
    ( ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( ( sk_C_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( zip_tseitin_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('204',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['138','205'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('207',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('208',plain,
    ( ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('210',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('211',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['208','211'])).

thf('213',plain,
    ( ! [X61: $i] :
        ( ( X61 = k1_xboole_0 )
        | ~ ( v1_finset_1 @ X61 )
        | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) )
    | ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('214',plain,(
    ! [X61: $i] :
      ( ( X61 = k1_xboole_0 )
      | ~ ( v1_finset_1 @ X61 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X61 ) @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','100','213'])).

thf('215',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['212','214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('217',plain,(
    zip_tseitin_0 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_waybel_0 @ X18 @ X19 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('219',plain,(
    v1_waybel_0 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    $false ),
    inference(demod,[status(thm)],['102','219'])).


%------------------------------------------------------------------------------
