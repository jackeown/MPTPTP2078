%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SlTK1s7Mjs

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:14 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 348 expanded)
%              Number of leaves         :   48 ( 120 expanded)
%              Depth                    :   28
%              Number of atoms          : 1572 (5729 expanded)
%              Number of equality atoms :   38 (  51 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(t8_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( ( r1_yellow_0 @ X27 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v1_yellow_0 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r2_lattice3 @ X29 @ k1_xboole_0 @ X28 )
      | ~ ( l1_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('7',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( X22
       != ( k1_yellow_0 @ X23 @ X24 ) )
      | ~ ( r1_yellow_0 @ X23 @ X24 )
      | ~ ( r2_lattice3 @ X23 @ X24 @ X25 )
      | ( r1_orders_2 @ X23 @ X22 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v5_orders_2 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( r1_orders_2 @ X23 @ ( k1_yellow_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r2_lattice3 @ X23 @ X24 @ X25 )
      | ~ ( r1_yellow_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( ( k3_yellow_0 @ X8 )
        = ( k1_yellow_0 @ X8 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('31',plain,(
    ! [X27: $i] :
      ( ( r1_yellow_0 @ X27 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v1_yellow_0 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r2_lattice3 @ X29 @ k1_xboole_0 @ X28 )
      | ~ ( l1_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( v5_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r2_hidden @ X32 @ X30 )
      | ~ ( r1_orders_2 @ X31 @ X33 @ X32 )
      | ~ ( r2_hidden @ X33 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','75'])).

thf('77',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('78',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('80',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['83','85'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('87',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('88',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('89',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ X2 @ X2 ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['84'])).

thf('96',plain,(
    ! [X8: $i] :
      ( ( ( k3_yellow_0 @ X8 )
        = ( k1_yellow_0 @ X8 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('97',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('99',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X9 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['96','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('109',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('110',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['84'])).

thf('114',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','94','95','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SlTK1s7Mjs
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.75  % Solved by: fo/fo7.sh
% 0.51/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.75  % done 516 iterations in 0.278s
% 0.51/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.75  % SZS output start Refutation
% 0.51/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.75  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.51/0.75  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.51/0.75  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.51/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.75  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.51/0.75  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.51/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.51/0.75  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.75  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.51/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.75  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.51/0.75  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.51/0.75  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.51/0.75  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.51/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.75  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.51/0.75  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.51/0.75  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.51/0.75  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.51/0.75  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.51/0.75  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.51/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.75  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.51/0.75  thf(t8_waybel_7, conjecture,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.51/0.75         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.51/0.75         ( l1_orders_2 @ A ) ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.51/0.75             ( v13_waybel_0 @ B @ A ) & 
% 0.51/0.75             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.75           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.51/0.75             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.51/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.75    (~( ![A:$i]:
% 0.51/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.51/0.75            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.51/0.75            ( l1_orders_2 @ A ) ) =>
% 0.51/0.75          ( ![B:$i]:
% 0.51/0.75            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.51/0.75                ( v13_waybel_0 @ B @ A ) & 
% 0.51/0.75                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.75              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.51/0.75                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.51/0.75    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.51/0.75  thf('0', plain,
% 0.51/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.51/0.75        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('1', plain,
% 0.51/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.51/0.75       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('split', [status(esa)], ['0'])).
% 0.51/0.75  thf(t42_yellow_0, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.51/0.75         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.51/0.75       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.51/0.75         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.75  thf('2', plain,
% 0.51/0.75      (![X27 : $i]:
% 0.51/0.75         ((r1_yellow_0 @ X27 @ k1_xboole_0)
% 0.51/0.75          | ~ (l1_orders_2 @ X27)
% 0.51/0.75          | ~ (v1_yellow_0 @ X27)
% 0.51/0.75          | ~ (v5_orders_2 @ X27)
% 0.51/0.75          | (v2_struct_0 @ X27))),
% 0.51/0.75      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.51/0.75  thf('3', plain,
% 0.51/0.75      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf(t49_subset_1, axiom,
% 0.51/0.75    (![A:$i,B:$i]:
% 0.51/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.75       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.51/0.75         ( ( A ) = ( B ) ) ) ))).
% 0.51/0.75  thf('4', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.51/0.75          | ((X1) = (X0))
% 0.51/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.51/0.75      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.51/0.75  thf('5', plain,
% 0.51/0.75      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.51/0.75           (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.75  thf(t6_yellow_0, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( l1_orders_2 @ A ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.51/0.75             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.51/0.75  thf('6', plain,
% 0.51/0.75      (![X28 : $i, X29 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.51/0.75          | (r2_lattice3 @ X29 @ k1_xboole_0 @ X28)
% 0.51/0.75          | ~ (l1_orders_2 @ X29))),
% 0.51/0.75      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.51/0.75  thf('7', plain,
% 0.51/0.75      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | ~ (l1_orders_2 @ sk_A)
% 0.51/0.75        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.51/0.75           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.75  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('9', plain,
% 0.51/0.75      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.51/0.75           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.51/0.75  thf('10', plain,
% 0.51/0.75      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.51/0.75           (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.75  thf(dt_k1_yellow_0, axiom,
% 0.51/0.75    (![A:$i,B:$i]:
% 0.51/0.75     ( ( l1_orders_2 @ A ) =>
% 0.51/0.75       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.51/0.75  thf('11', plain,
% 0.51/0.75      (![X9 : $i, X10 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X9)
% 0.51/0.75          | (m1_subset_1 @ (k1_yellow_0 @ X9 @ X10) @ (u1_struct_0 @ X9)))),
% 0.51/0.75      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.51/0.75  thf(t30_yellow_0, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75           ( ![C:$i]:
% 0.51/0.75             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.51/0.75                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.51/0.75                 ( ( ![D:$i]:
% 0.51/0.75                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.51/0.75                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.51/0.75                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.51/0.75               ( ( ( ![D:$i]:
% 0.51/0.75                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.51/0.75                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.51/0.75                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.51/0.75                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.51/0.75                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.51/0.75  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.51/0.75  thf(zf_stmt_2, axiom,
% 0.51/0.75    (![C:$i,B:$i,A:$i]:
% 0.51/0.75     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.51/0.75       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.51/0.75  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.51/0.75  thf(zf_stmt_4, axiom,
% 0.51/0.75    (![D:$i,C:$i,B:$i,A:$i]:
% 0.51/0.75     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.51/0.75       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.51/0.75  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.51/0.75  thf(zf_stmt_6, axiom,
% 0.51/0.75    (![D:$i,C:$i,B:$i,A:$i]:
% 0.51/0.75     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.51/0.75       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.51/0.75  thf(zf_stmt_7, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75           ( ![C:$i]:
% 0.51/0.75             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.51/0.75                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.51/0.75                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.51/0.75               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.51/0.75                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.51/0.75                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.51/0.75                   ( ![D:$i]:
% 0.51/0.75                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.51/0.75                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.75  thf('12', plain,
% 0.51/0.75      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.51/0.75          | ((X22) != (k1_yellow_0 @ X23 @ X24))
% 0.51/0.75          | ~ (r1_yellow_0 @ X23 @ X24)
% 0.51/0.75          | ~ (r2_lattice3 @ X23 @ X24 @ X25)
% 0.51/0.75          | (r1_orders_2 @ X23 @ X22 @ X25)
% 0.51/0.75          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.51/0.75          | ~ (l1_orders_2 @ X23)
% 0.51/0.75          | ~ (v5_orders_2 @ X23))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.51/0.75  thf('13', plain,
% 0.51/0.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.51/0.75         (~ (v5_orders_2 @ X23)
% 0.51/0.75          | ~ (l1_orders_2 @ X23)
% 0.51/0.75          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.51/0.75          | (r1_orders_2 @ X23 @ (k1_yellow_0 @ X23 @ X24) @ X25)
% 0.51/0.75          | ~ (r2_lattice3 @ X23 @ X24 @ X25)
% 0.51/0.75          | ~ (r1_yellow_0 @ X23 @ X24)
% 0.51/0.75          | ~ (m1_subset_1 @ (k1_yellow_0 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 0.51/0.75      inference('simplify', [status(thm)], ['12'])).
% 0.51/0.75  thf('14', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X0)
% 0.51/0.75          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.51/0.75          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.51/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.51/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | ~ (v5_orders_2 @ X0))),
% 0.51/0.75      inference('sup-', [status(thm)], ['11', '13'])).
% 0.51/0.75  thf('15', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.75         (~ (v5_orders_2 @ X0)
% 0.51/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.51/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.51/0.75          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.51/0.75          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.51/0.75          | ~ (l1_orders_2 @ X0))),
% 0.51/0.75      inference('simplify', [status(thm)], ['14'])).
% 0.51/0.75  thf('16', plain,
% 0.51/0.75      (![X0 : $i]:
% 0.51/0.75         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75          | ~ (l1_orders_2 @ sk_A)
% 0.51/0.75          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.51/0.75          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.51/0.75             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75          | ~ (v5_orders_2 @ sk_A))),
% 0.51/0.75      inference('sup-', [status(thm)], ['10', '15'])).
% 0.51/0.75  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('18', plain, ((v5_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('19', plain,
% 0.51/0.75      (![X0 : $i]:
% 0.51/0.75         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.51/0.75          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.51/0.75             (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.51/0.75  thf('20', plain,
% 0.51/0.75      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.51/0.75           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.51/0.75        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['9', '19'])).
% 0.51/0.75  thf('21', plain,
% 0.51/0.75      ((~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.51/0.75        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.51/0.75           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.51/0.75      inference('simplify', [status(thm)], ['20'])).
% 0.51/0.75  thf('22', plain,
% 0.51/0.75      (((v2_struct_0 @ sk_A)
% 0.51/0.75        | ~ (v5_orders_2 @ sk_A)
% 0.51/0.75        | ~ (v1_yellow_0 @ sk_A)
% 0.51/0.75        | ~ (l1_orders_2 @ sk_A)
% 0.51/0.75        | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.51/0.75           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['2', '21'])).
% 0.51/0.75  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('24', plain, ((v1_yellow_0 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('26', plain,
% 0.51/0.75      (((v2_struct_0 @ sk_A)
% 0.51/0.75        | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.51/0.75           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.51/0.75  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('28', plain,
% 0.51/0.75      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.51/0.75         (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.51/0.75      inference('clc', [status(thm)], ['26', '27'])).
% 0.51/0.75  thf('29', plain,
% 0.51/0.75      (![X9 : $i, X10 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X9)
% 0.51/0.75          | (m1_subset_1 @ (k1_yellow_0 @ X9 @ X10) @ (u1_struct_0 @ X9)))),
% 0.51/0.75      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.51/0.75  thf(d11_yellow_0, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( l1_orders_2 @ A ) =>
% 0.51/0.75       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.51/0.75  thf('30', plain,
% 0.51/0.75      (![X8 : $i]:
% 0.51/0.75         (((k3_yellow_0 @ X8) = (k1_yellow_0 @ X8 @ k1_xboole_0))
% 0.51/0.75          | ~ (l1_orders_2 @ X8))),
% 0.51/0.75      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.51/0.75  thf('31', plain,
% 0.51/0.75      (![X27 : $i]:
% 0.51/0.75         ((r1_yellow_0 @ X27 @ k1_xboole_0)
% 0.51/0.75          | ~ (l1_orders_2 @ X27)
% 0.51/0.75          | ~ (v1_yellow_0 @ X27)
% 0.51/0.75          | ~ (v5_orders_2 @ X27)
% 0.51/0.75          | (v2_struct_0 @ X27))),
% 0.51/0.75      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.51/0.75  thf('32', plain,
% 0.51/0.75      (![X9 : $i, X10 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X9)
% 0.51/0.75          | (m1_subset_1 @ (k1_yellow_0 @ X9 @ X10) @ (u1_struct_0 @ X9)))),
% 0.51/0.75      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.51/0.75  thf('33', plain,
% 0.51/0.75      (![X28 : $i, X29 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.51/0.75          | (r2_lattice3 @ X29 @ k1_xboole_0 @ X28)
% 0.51/0.75          | ~ (l1_orders_2 @ X29))),
% 0.51/0.75      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.51/0.75  thf('34', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X0)
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.75  thf('35', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | ~ (l1_orders_2 @ X0))),
% 0.51/0.75      inference('simplify', [status(thm)], ['34'])).
% 0.51/0.75  thf('36', plain,
% 0.51/0.75      (![X9 : $i, X10 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X9)
% 0.51/0.75          | (m1_subset_1 @ (k1_yellow_0 @ X9 @ X10) @ (u1_struct_0 @ X9)))),
% 0.51/0.75      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.51/0.75  thf('37', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.75         (~ (v5_orders_2 @ X0)
% 0.51/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.51/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.51/0.75          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.51/0.75          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.51/0.75          | ~ (l1_orders_2 @ X0))),
% 0.51/0.75      inference('simplify', [status(thm)], ['14'])).
% 0.51/0.75  thf('38', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X0)
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | ~ (r1_yellow_0 @ X0 @ X2)
% 0.51/0.75          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.51/0.75             (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | ~ (v5_orders_2 @ X0))),
% 0.51/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.75  thf('39', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.75         (~ (v5_orders_2 @ X0)
% 0.51/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.51/0.75             (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | ~ (r1_yellow_0 @ X0 @ X2)
% 0.51/0.75          | ~ (l1_orders_2 @ X0))),
% 0.51/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.51/0.75  thf('40', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X1)
% 0.51/0.75          | ~ (l1_orders_2 @ X1)
% 0.51/0.75          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 0.51/0.75          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.51/0.75             (k1_yellow_0 @ X1 @ X0))
% 0.51/0.75          | ~ (v5_orders_2 @ X1))),
% 0.51/0.75      inference('sup-', [status(thm)], ['35', '39'])).
% 0.51/0.75  thf('41', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v5_orders_2 @ X1)
% 0.51/0.75          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.51/0.75             (k1_yellow_0 @ X1 @ X0))
% 0.51/0.75          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 0.51/0.75          | ~ (l1_orders_2 @ X1))),
% 0.51/0.75      inference('simplify', [status(thm)], ['40'])).
% 0.51/0.75  thf('42', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         ((v2_struct_0 @ X0)
% 0.51/0.75          | ~ (v5_orders_2 @ X0)
% 0.51/0.75          | ~ (v1_yellow_0 @ X0)
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.51/0.75             (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | ~ (v5_orders_2 @ X0))),
% 0.51/0.75      inference('sup-', [status(thm)], ['31', '41'])).
% 0.51/0.75  thf('43', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.51/0.75           (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | ~ (v1_yellow_0 @ X0)
% 0.51/0.75          | ~ (v5_orders_2 @ X0)
% 0.51/0.75          | (v2_struct_0 @ X0))),
% 0.51/0.75      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.75  thf('44', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | (v2_struct_0 @ X0)
% 0.51/0.75          | ~ (v5_orders_2 @ X0)
% 0.51/0.75          | ~ (v1_yellow_0 @ X0)
% 0.51/0.75          | ~ (l1_orders_2 @ X0))),
% 0.51/0.75      inference('sup+', [status(thm)], ['30', '43'])).
% 0.51/0.75  thf('45', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (v1_yellow_0 @ X0)
% 0.51/0.75          | ~ (v5_orders_2 @ X0)
% 0.51/0.75          | (v2_struct_0 @ X0)
% 0.51/0.75          | ~ (l1_orders_2 @ X0)
% 0.51/0.75          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 0.51/0.75      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.75  thf('46', plain,
% 0.51/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('split', [status(esa)], ['0'])).
% 0.51/0.75  thf('47', plain,
% 0.51/0.75      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf(t4_subset, axiom,
% 0.51/0.75    (![A:$i,B:$i,C:$i]:
% 0.51/0.75     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.51/0.75       ( m1_subset_1 @ A @ C ) ))).
% 0.51/0.75  thf('48', plain,
% 0.51/0.75      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.75         (~ (r2_hidden @ X5 @ X6)
% 0.51/0.75          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.51/0.75          | (m1_subset_1 @ X5 @ X7))),
% 0.51/0.75      inference('cnf', [status(esa)], [t4_subset])).
% 0.51/0.75  thf('49', plain,
% 0.51/0.75      (![X0 : $i]:
% 0.51/0.75         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.75          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.51/0.75      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.75  thf('50', plain,
% 0.51/0.75      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['46', '49'])).
% 0.51/0.75  thf('51', plain,
% 0.51/0.75      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf(d20_waybel_0, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ( l1_orders_2 @ A ) =>
% 0.51/0.75       ( ![B:$i]:
% 0.51/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.75           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.51/0.75             ( ![C:$i]:
% 0.51/0.75               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75                 ( ![D:$i]:
% 0.51/0.75                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.75                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.51/0.75                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.75  thf('52', plain,
% 0.51/0.75      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.51/0.75          | ~ (v13_waybel_0 @ X30 @ X31)
% 0.51/0.75          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.51/0.75          | (r2_hidden @ X32 @ X30)
% 0.51/0.75          | ~ (r1_orders_2 @ X31 @ X33 @ X32)
% 0.51/0.75          | ~ (r2_hidden @ X33 @ X30)
% 0.51/0.75          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.51/0.75          | ~ (l1_orders_2 @ X31))),
% 0.51/0.75      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.51/0.75  thf('53', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ sk_A)
% 0.51/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.75          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.51/0.75          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.51/0.75          | (r2_hidden @ X1 @ sk_B_1)
% 0.51/0.75          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.75          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.51/0.75      inference('sup-', [status(thm)], ['51', '52'])).
% 0.51/0.75  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('55', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('56', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.75          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.51/0.75          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.51/0.75          | (r2_hidden @ X1 @ sk_B_1)
% 0.51/0.75          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.51/0.75  thf('57', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.75           | (r2_hidden @ X0 @ sk_B_1)
% 0.51/0.75           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.51/0.75           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['50', '56'])).
% 0.51/0.75  thf('58', plain,
% 0.51/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('split', [status(esa)], ['0'])).
% 0.51/0.75  thf('59', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.75           | (r2_hidden @ X0 @ sk_B_1)
% 0.51/0.75           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.75  thf('60', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          (~ (l1_orders_2 @ sk_A)
% 0.51/0.75           | (v2_struct_0 @ sk_A)
% 0.51/0.75           | ~ (v5_orders_2 @ sk_A)
% 0.51/0.75           | ~ (v1_yellow_0 @ sk_A)
% 0.51/0.75           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.51/0.75           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['45', '59'])).
% 0.51/0.75  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('62', plain, ((v5_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('63', plain, ((v1_yellow_0 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('64', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          ((v2_struct_0 @ sk_A)
% 0.51/0.75           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.51/0.75           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.51/0.75  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('66', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.51/0.75           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('clc', [status(thm)], ['64', '65'])).
% 0.51/0.75  thf('67', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          (~ (l1_orders_2 @ sk_A)
% 0.51/0.75           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['29', '66'])).
% 0.51/0.75  thf('68', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('69', plain,
% 0.51/0.75      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.75  thf('70', plain,
% 0.51/0.75      (![X0 : $i]:
% 0.51/0.75         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.75          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.51/0.75      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.75  thf('71', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['69', '70'])).
% 0.51/0.75  thf('72', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.75          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.51/0.75          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.51/0.75          | (r2_hidden @ X1 @ sk_B_1)
% 0.51/0.75          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.51/0.75  thf('73', plain,
% 0.51/0.75      ((![X0 : $i, X1 : $i]:
% 0.51/0.75          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.75           | (r2_hidden @ X1 @ sk_B_1)
% 0.51/0.75           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.51/0.75           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['71', '72'])).
% 0.51/0.75  thf('74', plain,
% 0.51/0.75      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.75  thf('75', plain,
% 0.51/0.75      ((![X0 : $i, X1 : $i]:
% 0.51/0.75          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.51/0.75           | (r2_hidden @ X1 @ sk_B_1)
% 0.51/0.75           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('demod', [status(thm)], ['73', '74'])).
% 0.51/0.75  thf('76', plain,
% 0.51/0.75      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75         | (r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.51/0.75         | ~ (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.51/0.75              (u1_struct_0 @ sk_A))))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['28', '75'])).
% 0.51/0.75  thf('77', plain,
% 0.51/0.75      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.51/0.75           (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.51/0.75  thf('78', plain,
% 0.51/0.75      ((((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.51/0.75         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('clc', [status(thm)], ['76', '77'])).
% 0.51/0.75  thf('79', plain,
% 0.51/0.75      (![X0 : $i, X1 : $i]:
% 0.51/0.75         (~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.51/0.75          | ((X1) = (X0))
% 0.51/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.51/0.75      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.51/0.75  thf('80', plain,
% 0.51/0.75      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.51/0.75         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['78', '79'])).
% 0.51/0.75  thf('81', plain,
% 0.51/0.75      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('82', plain,
% 0.51/0.75      (((((u1_struct_0 @ sk_A) = (sk_B_1)) | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('demod', [status(thm)], ['80', '81'])).
% 0.51/0.75  thf('83', plain,
% 0.51/0.75      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 0.51/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('simplify', [status(thm)], ['82'])).
% 0.51/0.75  thf('84', plain,
% 0.51/0.75      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.51/0.75        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('85', plain,
% 0.51/0.75      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('split', [status(esa)], ['84'])).
% 0.51/0.75  thf('86', plain,
% 0.51/0.75      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.51/0.75         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.51/0.75             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('sup+', [status(thm)], ['83', '85'])).
% 0.51/0.75  thf(rc3_subset_1, axiom,
% 0.51/0.75    (![A:$i]:
% 0.51/0.75     ( ?[B:$i]:
% 0.51/0.75       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.51/0.75         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.51/0.75  thf('87', plain, (![X2 : $i]: ~ (v1_subset_1 @ (sk_B @ X2) @ X2)),
% 0.51/0.75      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.51/0.75  thf('88', plain,
% 0.51/0.75      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.51/0.75      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.51/0.75  thf(d7_subset_1, axiom,
% 0.51/0.75    (![A:$i,B:$i]:
% 0.51/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.75       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.51/0.75  thf('89', plain,
% 0.51/0.75      (![X34 : $i, X35 : $i]:
% 0.51/0.75         (((X35) = (X34))
% 0.51/0.75          | (v1_subset_1 @ X35 @ X34)
% 0.51/0.75          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.51/0.75      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.51/0.75  thf('90', plain,
% 0.51/0.75      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['88', '89'])).
% 0.51/0.75  thf('91', plain, (![X2 : $i]: ~ (v1_subset_1 @ (sk_B @ X2) @ X2)),
% 0.51/0.75      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.51/0.75  thf('92', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.51/0.75      inference('clc', [status(thm)], ['90', '91'])).
% 0.51/0.75  thf('93', plain, (![X2 : $i]: ~ (v1_subset_1 @ X2 @ X2)),
% 0.51/0.75      inference('demod', [status(thm)], ['87', '92'])).
% 0.51/0.75  thf('94', plain,
% 0.51/0.75      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.51/0.75       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['86', '93'])).
% 0.51/0.75  thf('95', plain,
% 0.51/0.75      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.51/0.75       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('split', [status(esa)], ['84'])).
% 0.51/0.75  thf('96', plain,
% 0.51/0.75      (![X8 : $i]:
% 0.51/0.75         (((k3_yellow_0 @ X8) = (k1_yellow_0 @ X8 @ k1_xboole_0))
% 0.51/0.75          | ~ (l1_orders_2 @ X8))),
% 0.51/0.75      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.51/0.75  thf('97', plain,
% 0.51/0.75      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('98', plain,
% 0.51/0.75      (![X34 : $i, X35 : $i]:
% 0.51/0.75         (((X35) = (X34))
% 0.51/0.75          | (v1_subset_1 @ X35 @ X34)
% 0.51/0.75          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.51/0.75      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.51/0.75  thf('99', plain,
% 0.51/0.75      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.51/0.75        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.51/0.75  thf('100', plain,
% 0.51/0.75      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('split', [status(esa)], ['0'])).
% 0.51/0.75  thf('101', plain,
% 0.51/0.75      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['99', '100'])).
% 0.51/0.75  thf('102', plain,
% 0.51/0.75      (![X9 : $i, X10 : $i]:
% 0.51/0.75         (~ (l1_orders_2 @ X9)
% 0.51/0.75          | (m1_subset_1 @ (k1_yellow_0 @ X9 @ X10) @ (u1_struct_0 @ X9)))),
% 0.51/0.75      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.51/0.75  thf('103', plain,
% 0.51/0.75      ((![X0 : $i]:
% 0.51/0.75          ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 0.51/0.75           | ~ (l1_orders_2 @ sk_A)))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('sup+', [status(thm)], ['101', '102'])).
% 0.51/0.75  thf('104', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('105', plain,
% 0.51/0.75      ((![X0 : $i]: (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('demod', [status(thm)], ['103', '104'])).
% 0.51/0.75  thf('106', plain,
% 0.51/0.75      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1) | ~ (l1_orders_2 @ sk_A)))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('sup+', [status(thm)], ['96', '105'])).
% 0.51/0.75  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('108', plain,
% 0.51/0.75      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('demod', [status(thm)], ['106', '107'])).
% 0.51/0.75  thf(t2_subset, axiom,
% 0.51/0.75    (![A:$i,B:$i]:
% 0.51/0.75     ( ( m1_subset_1 @ A @ B ) =>
% 0.51/0.75       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.51/0.75  thf('109', plain,
% 0.51/0.75      (![X3 : $i, X4 : $i]:
% 0.51/0.75         ((r2_hidden @ X3 @ X4)
% 0.51/0.75          | (v1_xboole_0 @ X4)
% 0.51/0.75          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.51/0.75      inference('cnf', [status(esa)], [t2_subset])).
% 0.51/0.75  thf('110', plain,
% 0.51/0.75      ((((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('sup-', [status(thm)], ['108', '109'])).
% 0.51/0.75  thf('111', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.75  thf('112', plain,
% 0.51/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.51/0.75         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.75      inference('clc', [status(thm)], ['110', '111'])).
% 0.51/0.75  thf('113', plain,
% 0.51/0.75      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.51/0.75         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.51/0.75      inference('split', [status(esa)], ['84'])).
% 0.51/0.75  thf('114', plain,
% 0.51/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.51/0.75       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.75      inference('sup-', [status(thm)], ['112', '113'])).
% 0.51/0.75  thf('115', plain, ($false),
% 0.51/0.75      inference('sat_resolution*', [status(thm)], ['1', '94', '95', '114'])).
% 0.51/0.75  
% 0.51/0.75  % SZS output end Refutation
% 0.51/0.75  
% 0.51/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
