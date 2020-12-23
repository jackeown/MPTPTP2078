%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1695+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IatbqgFQG7

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:04 EST 2020

% Result     : Theorem 6.99s
% Output     : Refutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :  375 (120346 expanded)
%              Number of leaves         :   44 (31946 expanded)
%              Depth                    :   73
%              Number of atoms          : 5504 (2579099 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v24_waybel_0_type,type,(
    v24_waybel_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(t75_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v24_waybel_0 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( r1_yellow_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( v24_waybel_0 @ A )
        <=> ! [B: $i] :
              ( ( ~ ( v1_xboole_0 @ B )
                & ( v1_waybel_0 @ B @ A )
                & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( r1_yellow_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_waybel_0])).

thf('0',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_B_1 )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X41: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_waybel_0 @ X41 @ sk_A )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ( v24_waybel_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v24_waybel_0 @ sk_A )
    | ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d39_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v24_waybel_0 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ? [C: $i] :
                ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r3_orders_2 @ A @ C @ D ) ) )
                & ( r2_lattice3 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_waybel_0 @ ( sk_B @ X0 ) @ X0 )
      | ( v24_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v24_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('6',plain,
    ( ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d7_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
              & ( r2_lattice3 @ A @ B @ C )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ C @ D ) ) )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( r2_lattice3 @ A @ B @ E )
                           => ( r1_orders_2 @ A @ D @ E ) ) )
                      & ( r2_lattice3 @ A @ B @ D ) )
                   => ( D = C ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_4 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_3 @ D @ C @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ B @ A )
       => ( D = C ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ B @ A )
    <=> ( ( r2_lattice3 @ A @ B @ D )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
           => ( ( r2_lattice3 @ A @ B @ E )
             => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_lattice3 @ A @ B @ D )
       => ( r1_orders_2 @ A @ C @ D ) ) ) )).

thf(zf_stmt_11,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( zip_tseitin_4 @ D @ C @ B @ A )
              & ! [D: $i] :
                  ( zip_tseitin_1 @ D @ C @ B @ A )
              & ( r2_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_yellow_0 @ X31 @ X32 )
      | ( r2_lattice3 @ X31 @ X32 @ ( sk_C_1 @ X32 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('17',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_yellow_0 @ X31 @ X32 )
      | ( m1_subset_1 @ ( sk_C_1 @ X32 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('22',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v24_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('27',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ X1 )
      | ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ ( sk_D @ X1 @ X0 ) )
      | ( v24_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('37',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( r1_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_yellow_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ ( sk_C_1 @ X32 @ X31 ) @ X32 @ X31 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v24_waybel_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v24_waybel_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ( zip_tseitin_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X10 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('51',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ( v24_waybel_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_lattice3 @ X4 @ X5 @ X6 )
      | ( r1_orders_2 @ X4 @ X7 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('55',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['43','55'])).

thf('57',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('59',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( r3_orders_2 @ X36 @ X35 @ X37 )
      | ~ ( r1_orders_2 @ X36 @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ( v24_waybel_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ( v24_waybel_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v24_waybel_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['33','66'])).

thf('68',plain,
    ( ( ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ ( sk_B @ X0 ) @ X1 )
      | ~ ( r3_orders_2 @ X0 @ X1 @ ( sk_D @ X1 @ X0 ) )
      | ( v24_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['19','77'])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v24_waybel_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v24_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('83',plain,
    ( ( ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v24_waybel_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v24_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v24_waybel_0 @ sk_A ) )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v24_waybel_0 @ sk_A )
   <= ! [X41: $i] :
        ( ( v1_xboole_0 @ X41 )
        | ~ ( v1_waybel_0 @ X41 @ sk_A )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_yellow_0 @ sk_A @ X41 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v24_waybel_0 @ sk_A )
   <= ~ ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ~ ! [X41: $i] :
          ( ( v1_xboole_0 @ X41 )
          | ~ ( v1_waybel_0 @ X41 @ sk_A )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( r1_yellow_0 @ sk_A @ X41 ) )
    | ( v24_waybel_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_B_1 )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','91','92'])).

thf('94',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','93'])).

thf('95',plain,
    ( ( v24_waybel_0 @ sk_A )
   <= ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('96',plain,
    ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v24_waybel_0 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( sk_C @ X2 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_waybel_0 @ X2 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v24_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v24_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ~ ( v24_waybel_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    v24_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91'])).

thf('110',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['98'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','91','110'])).

thf('112',plain,
    ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['96'])).

thf('113',plain,(
    v1_waybel_0 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91','112'])).

thf('114',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['108','109','111','113'])).

thf('115',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['115'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','91','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['116','118'])).

thf('120',plain,(
    r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X15 @ X18 )
      | ( m1_subset_1 @ ( sk_E @ X18 @ X15 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_lattice3 @ X18 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('122',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','119'])).

thf('124',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X15 @ X18 )
      | ( r2_lattice3 @ X18 @ X15 @ ( sk_E @ X18 @ X15 @ X16 ) )
      | ~ ( r2_lattice3 @ X18 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('125',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('127',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X15 @ X18 )
      | ( m1_subset_1 @ ( sk_E @ X18 @ X15 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_lattice3 @ X18 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('128',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v24_waybel_0 @ sk_A )
   <= ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('130',plain,
    ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['96'])).

thf('131',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['98'])).

thf('132',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( v24_waybel_0 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ X3 )
      | ( r3_orders_2 @ X0 @ ( sk_C @ X2 @ X0 ) @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_waybel_0 @ X2 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 )
        | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( v24_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 )
        | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( v24_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ~ ( v24_waybel_0 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ X0 )
        | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ X0 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','137'])).

thf('139',plain,
    ( ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','138'])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    v24_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91'])).

thf('142',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','91','110'])).

thf('143',plain,(
    v1_waybel_0 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91','112'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( v24_waybel_0 @ sk_A )
   <= ( v24_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('148',plain,
    ( ( v1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( v1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['96'])).

thf('149',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['98'])).

thf('150',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v24_waybel_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_waybel_0 @ X2 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d39_waybel_0])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v24_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v24_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( ~ ( v24_waybel_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    v24_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91'])).

thf('160',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','91','110'])).

thf('161',plain,(
    v1_waybel_0 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91','112'])).

thf('162',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['158','159','160','161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['116','118'])).

thf('164',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( r1_orders_2 @ X36 @ X35 @ X37 )
      | ~ ( r3_orders_2 @ X36 @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','169'])).

thf('171',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','171'])).

thf('173',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X15 @ X18 )
      | ~ ( r1_orders_2 @ X18 @ X16 @ ( sk_E @ X18 @ X15 @ X16 ) )
      | ~ ( r2_lattice3 @ X18 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('175',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','119'])).

thf('177',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['116','118'])).

thf('182',plain,(
    zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['180','181'])).

thf('184',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X8 )
      | ( r2_lattice3 @ X8 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('185',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X23 )
      | ( zip_tseitin_2 @ X19 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('188',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('189',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X16 @ X17 )
      | ~ ( r2_lattice3 @ X14 @ X15 @ X17 )
      | ~ ( zip_tseitin_2 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X4 @ X0 )
      | ~ ( zip_tseitin_2 @ X3 @ X2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_3 @ X2 @ X6 @ X1 @ X0 )
      | ( r1_orders_2 @ X0 @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X5 @ X4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_1 @ X0 @ X7 @ X1 @ X2 )
      | ( zip_tseitin_1 @ X0 @ X4 @ X3 @ X2 )
      | ( r1_orders_2 @ X2 @ X5 @ X0 )
      | ( zip_tseitin_3 @ X5 @ X6 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_3 @ X5 @ X4 @ X1 @ X0 )
      | ( r1_orders_2 @ X0 @ X5 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['192'])).

thf('194',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X8 )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_1 @ X0 @ X5 @ X4 @ X2 )
      | ( zip_tseitin_3 @ X1 @ X6 @ X4 @ X2 )
      | ( zip_tseitin_0 @ X0 @ X1 @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_3 @ X2 @ X5 @ X4 @ X0 )
      | ( zip_tseitin_1 @ X3 @ X6 @ X4 @ X0 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X4 @ X1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['197'])).

thf('199',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_2 @ X19 @ X20 @ X21 )
      | ( X19 = X22 )
      | ~ ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_1 @ X4 @ X3 @ X1 @ X0 )
      | ( X3 = X2 )
      | ~ ( zip_tseitin_2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','200'])).

thf('202',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('203',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('204',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('205',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ X0 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','137'])).

thf('206',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['203','207'])).

thf('209',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('213',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( r1_orders_2 @ X36 @ X35 @ X37 )
      | ~ ( r3_orders_2 @ X36 @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('214',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B_1 )
        | ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B_1 )
        | ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','217'])).

thf('219',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['202','219'])).

thf('221',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    v24_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91'])).

thf('225',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','91','110'])).

thf('226',plain,(
    v1_waybel_0 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91','112'])).

thf('227',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['223','224','225','226'])).

thf('228',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['116','118'])).

thf('229',plain,(
    r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X8 )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('231',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('233',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['201','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['234'])).

thf('236',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('237',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X23 )
      | ( zip_tseitin_2 @ X19 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('238',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ~ ( zip_tseitin_3 @ X24 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('239',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_2 @ X3 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( r2_lattice3 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X31 ) )
      | ( r1_yellow_0 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_4 @ X1 @ X4 @ X3 @ X0 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X1 @ X2 @ X0 ) @ X1 @ X2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ X1 @ X2 @ X0 ) @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['236','241'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['235','242'])).

thf('244',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','119'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B_1 )
      | ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','93'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['246','247'])).

thf('249',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('250',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( zip_tseitin_3 @ X24 @ X26 @ X27 @ X25 )
      | ~ ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['248','251'])).

thf('253',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_2 @ X19 @ X20 @ X21 )
      | ( X19 = X22 )
      | ~ ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = X1 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','254'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( zip_tseitin_2 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['234'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','200'])).

thf('263',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['262','263'])).

thf('265',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('266',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( r2_lattice3 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X31 ) )
      | ( r1_yellow_0 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['264','267'])).

thf('269',plain,(
    r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','119'])).

thf('270',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('271',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['268','269','270','271'])).

thf('273',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(condensation,[status(thm)],['272'])).

thf('274',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','93'])).

thf('275',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X10 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['261','277'])).

thf('279',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_lattice3 @ X4 @ X5 @ X6 )
      | ( r1_orders_2 @ X4 @ X7 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('280',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['260','280'])).

thf('282',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X23 )
      | ( zip_tseitin_2 @ X19 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('283',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('284',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('285',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X16 @ X17 )
      | ~ ( r2_lattice3 @ X14 @ X15 @ X17 )
      | ~ ( zip_tseitin_2 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('286',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ sk_B_1 )
        | ~ ( zip_tseitin_2 @ X1 @ X0 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B_1 )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['283','286'])).

thf('288',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v24_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v1_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,(
    v24_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91'])).

thf('290',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','91','110'])).

thf('291',plain,(
    v1_waybel_0 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','91','112'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['288','289','290','291'])).

thf('293',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['116','118'])).

thf('294',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ X1 @ sk_B_1 @ sk_A )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['282','294'])).

thf('296',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf(t25_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('297',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_orders_2 @ X39 @ X38 @ X40 )
      | ~ ( r1_orders_2 @ X39 @ X40 @ X38 )
      | ( X38 = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 )
      | ~ ( v5_orders_2 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('298',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['296','297'])).

thf('299',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X0 @ X1 @ sk_B_1 @ sk_A )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['295','301'])).

thf('303',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['281','302'])).

thf('304',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('305',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['305'])).

thf('307',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ~ ( zip_tseitin_3 @ X24 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('308',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( zip_tseitin_4 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( r2_lattice3 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X31 ) )
      | ( r1_yellow_0 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('310',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( zip_tseitin_1 @ ( sk_D_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('313',plain,(
    r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','119'])).

thf('314',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['234'])).

thf('315',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['310','311','312','313','314'])).

thf('316',plain,(
    ~ ( r1_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','93'])).

thf('317',plain,
    ( ( sk_C @ sk_B_1 @ sk_A )
    = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['315','316'])).

thf('318',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( r2_lattice3 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X31 ) )
      | ( r1_yellow_0 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('319',plain,
    ( ~ ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( zip_tseitin_1 @ ( sk_D_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X23 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('321',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( zip_tseitin_3 @ X22 @ X22 @ X20 @ X23 ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ~ ( zip_tseitin_3 @ X24 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('323',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_4 @ X2 @ X2 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('326',plain,(
    r2_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','119'])).

thf('327',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['234'])).

thf('328',plain,(
    r1_yellow_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['319','323','324','325','326','327'])).

thf('329',plain,(
    $false ),
    inference(demod,[status(thm)],['94','328'])).


%------------------------------------------------------------------------------
