%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1696+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2ABB54lTsU

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:05 EST 2020

% Result     : Theorem 5.62s
% Output     : Refutation 5.62s
% Verified   : 
% Statistics : Number of formulae       :  304 (46034 expanded)
%              Number of leaves         :   41 (12113 expanded)
%              Depth                    :   59
%              Number of atoms          : 4040 (862499 expanded)
%              Number of equality atoms :   27 (  80 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v25_waybel_0_type,type,(
    v25_waybel_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(t76_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v25_waybel_0 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( r2_yellow_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( v25_waybel_0 @ A )
        <=> ! [B: $i] :
              ( ( ~ ( v1_xboole_0 @ B )
                & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( r2_yellow_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_waybel_0])).

thf('0',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B_1 )
    | ~ ( v25_waybel_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B_1 )
   <= ~ ( r2_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X38: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_yellow_0 @ sk_A @ X38 )
      | ( v25_waybel_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v25_waybel_0 @ sk_A )
    | ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d40_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v25_waybel_0 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ? [C: $i] :
                ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) )
                & ( r1_lattice3 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v25_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('5',plain,
    ( ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(d8_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
              & ( r1_lattice3 @ A @ B @ C )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ D @ C ) ) )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( r1_lattice3 @ A @ B @ E )
                           => ( r1_orders_2 @ A @ E @ D ) ) )
                      & ( r1_lattice3 @ A @ B @ D ) )
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
    <=> ( ( r1_lattice3 @ A @ B @ D )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
           => ( ( r1_lattice3 @ A @ B @ E )
             => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) )).

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
    <=> ( ( r1_lattice3 @ A @ B @ D )
       => ( r1_orders_2 @ A @ D @ C ) ) ) )).

thf(zf_stmt_11,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( zip_tseitin_4 @ D @ C @ B @ A )
              & ! [D: $i] :
                  ( zip_tseitin_1 @ D @ C @ B @ A )
              & ( r1_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_yellow_0 @ X31 @ X32 )
      | ( r1_lattice3 @ X31 @ X32 @ ( sk_C_1 @ X32 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('11',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('15',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_yellow_0 @ X31 @ X32 )
      | ( m1_subset_1 @ ( sk_C_1 @ X32 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('17',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ ( sk_B @ X0 ) @ X1 )
      | ( r1_lattice3 @ X0 @ ( sk_B @ X0 ) @ ( sk_D @ X1 @ X0 ) )
      | ( v25_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('21',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,
    ( ( ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('29',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_yellow_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ ( sk_C_1 @ X32 @ X31 ) @ X32 @ X31 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ( v25_waybel_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ( v25_waybel_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('34',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ ( sk_B @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v25_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X10 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v25_waybel_0 @ sk_A )
        | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
        | ~ ( zip_tseitin_1 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_lattice3 @ X4 @ X5 @ X6 )
      | ( r1_orders_2 @ X4 @ X6 @ X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['27','48'])).

thf('50',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ ( sk_B @ X0 ) @ X1 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_D @ X1 @ X0 ) @ X1 )
      | ( v25_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['13','59'])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v25_waybel_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v25_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('65',plain,
    ( ( ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v25_waybel_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v25_waybel_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v25_waybel_0 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v25_waybel_0 @ sk_A )
   <= ! [X38: $i] :
        ( ( v1_xboole_0 @ X38 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_yellow_0 @ sk_A @ X38 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v25_waybel_0 @ sk_A )
   <= ~ ( v25_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ~ ! [X38: $i] :
          ( ( v1_xboole_0 @ X38 )
          | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( r2_yellow_0 @ sk_A @ X38 ) )
    | ( v25_waybel_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B_1 )
    | ~ ( v25_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,(
    ~ ( r2_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','73','74'])).

thf('76',plain,(
    ~ ( r2_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','75'])).

thf('77',plain,
    ( ( v25_waybel_0 @ sk_A )
   <= ( v25_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v25_waybel_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v25_waybel_0 @ X0 )
      | ( r1_lattice3 @ X0 @ X2 @ ( sk_C @ X2 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v25_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v25_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    v25_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','73'])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v25_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','73','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['87','88','90'])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v25_waybel_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v25_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','73','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('97',plain,(
    r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X15 @ X18 )
      | ( m1_subset_1 @ ( sk_E @ X18 @ X15 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_lattice3 @ X18 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('99',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('101',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X15 @ X18 )
      | ( r1_lattice3 @ X18 @ X15 @ ( sk_E @ X18 @ X15 @ X16 ) )
      | ~ ( r1_lattice3 @ X18 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('102',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v25_waybel_0 @ sk_A )
   <= ( v25_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['78'])).

thf('105',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( v25_waybel_0 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X3 )
      | ( r1_orders_2 @ X0 @ X3 @ ( sk_C @ X2 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( v25_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ X0 )
        | ~ ( v25_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,
    ( ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','110'])).

thf('112',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    v25_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','73'])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','73','89'])).

thf('115',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','115'])).

thf('117',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_E @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X15 @ X18 )
      | ~ ( r1_orders_2 @ X18 @ ( sk_E @ X18 @ X15 @ X16 ) @ X16 )
      | ~ ( r1_lattice3 @ X18 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('119',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['91','96'])).

thf('121',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('126',plain,(
    zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['124','125'])).

thf('128',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X8 )
      | ( r1_lattice3 @ X8 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('129',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X23 )
      | ( zip_tseitin_2 @ X19 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('132',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('133',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X17 @ X16 )
      | ~ ( r1_lattice3 @ X14 @ X15 @ X17 )
      | ~ ( zip_tseitin_2 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X4 @ X0 )
      | ~ ( zip_tseitin_2 @ X3 @ X2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_3 @ X2 @ X6 @ X1 @ X0 )
      | ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X5 @ X4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_1 @ X0 @ X7 @ X1 @ X2 )
      | ( zip_tseitin_1 @ X0 @ X4 @ X3 @ X2 )
      | ( r1_orders_2 @ X2 @ X0 @ X5 )
      | ( zip_tseitin_3 @ X5 @ X6 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_3 @ X5 @ X4 @ X1 @ X0 )
      | ( r1_orders_2 @ X0 @ X3 @ X5 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['136'])).

thf('138',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X8 )
      | ~ ( r1_orders_2 @ X8 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_1 @ X1 @ X5 @ X4 @ X2 )
      | ( zip_tseitin_3 @ X0 @ X6 @ X4 @ X2 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_3 @ X2 @ X5 @ X4 @ X0 )
      | ( zip_tseitin_1 @ X3 @ X6 @ X4 @ X0 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X4 @ X1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['141'])).

thf('143',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_2 @ X19 @ X20 @ X21 )
      | ( X19 = X22 )
      | ~ ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_1 @ X4 @ X3 @ X1 @ X0 )
      | ( X3 = X2 )
      | ~ ( zip_tseitin_2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','144'])).

thf('146',plain,
    ( ( v25_waybel_0 @ sk_A )
   <= ( v25_waybel_0 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('147',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['78'])).

thf('148',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v25_waybel_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d40_waybel_0])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v25_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v25_waybel_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('158',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['155','159'])).

thf('161',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    v25_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','73'])).

thf('165',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','73','89'])).

thf('166',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('168',plain,(
    r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X8 )
      | ~ ( r1_orders_2 @ X8 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('170',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X13 )
      | ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('172',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ sk_A )
      | ( zip_tseitin_1 @ X2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['145','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['173'])).

thf('175',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('176',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X23 )
      | ( zip_tseitin_2 @ X19 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('177',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ~ ( zip_tseitin_3 @ X24 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_2 @ X3 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( r1_lattice3 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X31 ) )
      | ( r2_yellow_0 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_4 @ X1 @ X4 @ X3 @ X0 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X1 @ X2 @ X0 ) @ X1 @ X2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X2 @ X1 )
      | ( r2_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ X1 @ X2 @ X0 ) @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B_1 )
      | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','181'])).

thf('183',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['91','96'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B_1 )
      | ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ~ ( r2_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','75'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('189',plain,(
    v25_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','73'])).

thf('190',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','73','89'])).

thf('191',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('193',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( zip_tseitin_3 @ X24 @ X26 @ X27 @ X25 )
      | ~ ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['187','195'])).

thf('197',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_2 @ X19 @ X20 @ X21 )
      | ( X19 = X22 )
      | ~ ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = X1 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','198'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_lattice3 @ X14 @ X15 @ X16 )
      | ~ ( zip_tseitin_2 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['173'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','144'])).

thf('207',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ X1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('210',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( r1_lattice3 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X31 ) )
      | ( r2_yellow_0 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['208','211'])).

thf('213',plain,(
    r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['91','96'])).

thf('214',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('215',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['212','213','214','215'])).

thf('217',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(condensation,[status(thm)],['216'])).

thf('218',plain,(
    ~ ( r2_yellow_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','75'])).

thf('219',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X10 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X12 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['205','221'])).

thf('223',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_lattice3 @ X4 @ X5 @ X6 )
      | ( r1_orders_2 @ X4 @ X6 @ X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('224',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['204','224'])).

thf('226',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['191','192'])).

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

thf('227',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_orders_2 @ X36 @ X35 @ X37 )
      | ~ ( r1_orders_2 @ X36 @ X37 @ X35 )
      | ( X35 = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = X0 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['225','231'])).

thf('233',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( ( sk_C @ sk_B_1 @ sk_A )
        = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ),
    inference(condensation,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('237',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('238',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('239',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X17 @ X16 )
      | ~ ( r1_lattice3 @ X14 @ X15 @ X17 )
      | ~ ( zip_tseitin_2 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('240',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v1_xboole_0 @ sk_B_1 )
        | ~ ( zip_tseitin_2 @ X1 @ X0 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X1 ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B_1 )
        | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A )
        | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['237','240'])).

thf('242',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A )
        | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( v25_waybel_0 @ sk_A )
      & ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    v25_waybel_0 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','73'])).

thf('244',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','73','89'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['242','243','244'])).

thf('246',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( zip_tseitin_2 @ X0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['236','247'])).

thf('249',plain,
    ( ( sk_C @ sk_B_1 @ sk_A )
    = ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['235','248'])).

thf('250',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_2 @ X29 @ X30 @ X31 ) @ X29 @ X30 @ X31 )
      | ~ ( r1_lattice3 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X31 ) )
      | ( r2_yellow_0 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('251',plain,
    ( ~ ( zip_tseitin_4 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( zip_tseitin_1 @ ( sk_D_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_3 @ X19 @ X22 @ X20 @ X23 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('253',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( zip_tseitin_3 @ X22 @ X22 @ X20 @ X23 ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_4 @ X24 @ X26 @ X27 @ X28 )
      | ~ ( zip_tseitin_3 @ X24 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('255',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_4 @ X2 @ X2 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('258',plain,(
    r1_lattice3 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['91','96'])).

thf('259',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ),
    inference(condensation,[status(thm)],['173'])).

thf('260',plain,(
    r2_yellow_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['251','255','256','257','258','259'])).

thf('261',plain,(
    $false ),
    inference(demod,[status(thm)],['76','260'])).


%------------------------------------------------------------------------------
