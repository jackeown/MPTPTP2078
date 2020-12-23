%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bd5BgKbLSh

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:10 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 224 expanded)
%              Number of leaves         :   51 (  95 expanded)
%              Depth                    :   22
%              Number of atoms          : 1020 (1967 expanded)
%              Number of equality atoms :   22 (  71 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t13_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( r2_hidden @ k1_xboole_0 @ A )
         => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( ( k3_yellow_0 @ X16 )
        = ( k1_yellow_0 @ X16 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('2',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ( r2_lattice3 @ X34 @ k1_xboole_0 @ X33 )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

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

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X23 @ X24 )
      | ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

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

thf('15',plain,(
    ! [X28: $i,X29: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_lattice3 @ X29 @ X32 @ X28 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X32 @ X28 @ X29 ) @ X32 @ X28 @ X29 )
      | ( zip_tseitin_2 @ X32 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X40: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('18',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('23',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('25',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ ( k2_yellow_1 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X45 ) @ X44 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ ( k2_yellow_1 @ X45 ) ) )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('27',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('28',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('29',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X45 ) @ X44 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ X45 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X13 @ X15 )
      | ~ ( r3_orders_2 @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('46',plain,(
    ! [X38: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('47',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('51',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X21 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('59',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('61',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X27
        = ( k1_yellow_0 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_2 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','65'])).

thf('67',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('68',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X41: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X41 ) )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('72',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bd5BgKbLSh
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:30:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 120 iterations in 0.095s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.38/0.55  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.38/0.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.38/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.38/0.55  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.38/0.55  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.38/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.38/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.38/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.38/0.55  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.38/0.55  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.38/0.55  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.38/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.38/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.55  thf(t13_yellow_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.55       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.38/0.55         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.55          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.38/0.55            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.38/0.55  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d11_yellow_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_orders_2 @ A ) =>
% 0.38/0.55       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X16 : $i]:
% 0.38/0.55         (((k3_yellow_0 @ X16) = (k1_yellow_0 @ X16 @ k1_xboole_0))
% 0.38/0.55          | ~ (l1_orders_2 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.38/0.55  thf('2', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t1_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.38/0.55  thf('4', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf(t1_yellow_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.38/0.55       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.55  thf('5', plain, (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.55  thf(t6_yellow_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_orders_2 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.38/0.55             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X33 : $i, X34 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 0.38/0.55          | (r2_lattice3 @ X34 @ k1_xboole_0 @ X33)
% 0.38/0.55          | ~ (l1_orders_2 @ X34))),
% 0.38/0.55      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.55  thf(dt_k2_yellow_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.55       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.38/0.55  thf('8', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.38/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '9'])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.55  thf(t30_yellow_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.38/0.55                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.38/0.55                 ( ( ![D:$i]:
% 0.38/0.55                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.38/0.55                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.38/0.55                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.38/0.55               ( ( ( ![D:$i]:
% 0.38/0.55                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.38/0.55                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.38/0.55                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.38/0.55                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.38/0.55                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_1, axiom,
% 0.38/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.55     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.38/0.55       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.55         ((zip_tseitin_1 @ X21 @ X22 @ X23 @ X24)
% 0.38/0.55          | (m1_subset_1 @ X21 @ (u1_struct_0 @ X24)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.55  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.38/0.55  thf(zf_stmt_3, axiom,
% 0.38/0.55    (![C:$i,B:$i,A:$i]:
% 0.38/0.55     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.38/0.55       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.38/0.55  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.38/0.55  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.55  thf(zf_stmt_6, axiom,
% 0.38/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.55     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.38/0.55       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.38/0.55  thf(zf_stmt_7, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.38/0.55                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.38/0.55                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.38/0.55               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.38/0.55                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.38/0.55                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.38/0.55                   ( ![D:$i]:
% 0.38/0.55                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.55                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.38/0.55                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X28 : $i, X29 : $i, X32 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.38/0.55          | ~ (r2_lattice3 @ X29 @ X32 @ X28)
% 0.38/0.55          | ~ (zip_tseitin_1 @ (sk_D @ X32 @ X28 @ X29) @ X32 @ X28 @ X29)
% 0.38/0.55          | (zip_tseitin_2 @ X32 @ X28 @ X29)
% 0.38/0.55          | ~ (l1_orders_2 @ X29)
% 0.38/0.55          | ~ (v5_orders_2 @ X29))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.38/0.55               X1 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.55  thf(fc5_yellow_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.55       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.55       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.55       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.38/0.55  thf('17', plain, (![X40 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X40))),
% 0.38/0.55      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.38/0.55  thf('18', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.38/0.55               X1 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.38/0.55      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((m1_subset_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.38/0.55          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.38/0.55          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['13', '19'])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      ((~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.38/0.55        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (m1_subset_1 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['10', '20'])).
% 0.38/0.55  thf('22', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (m1_subset_1 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (m1_subset_1 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('25', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf(t3_yellow_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.38/0.55               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.38/0.55                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ (k2_yellow_1 @ X45)))
% 0.38/0.55          | ~ (r1_tarski @ X44 @ X46)
% 0.38/0.55          | (r3_orders_2 @ (k2_yellow_1 @ X45) @ X44 @ X46)
% 0.38/0.55          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ (k2_yellow_1 @ X45)))
% 0.38/0.55          | (v1_xboole_0 @ X45))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X44 @ X45)
% 0.38/0.55          | ~ (r1_tarski @ X44 @ X46)
% 0.38/0.55          | (r3_orders_2 @ (k2_yellow_1 @ X45) @ X44 @ X46)
% 0.38/0.55          | ~ (m1_subset_1 @ X46 @ X45)
% 0.38/0.55          | (v1_xboole_0 @ X45))),
% 0.38/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.38/0.55          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.38/0.55          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['25', '29'])).
% 0.38/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.55  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.55  thf(d3_tarski, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X1 : $i, X3 : $i]:
% 0.38/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf(t4_subset_1, axiom,
% 0.38/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.55  thf(t5_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X10 @ X11)
% 0.38/0.55          | ~ (v1_xboole_0 @ X12)
% 0.38/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['32', '35'])).
% 0.38/0.55  thf('37', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.55      inference('sup-', [status(thm)], ['31', '36'])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v1_xboole_0 @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.38/0.55          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['30', '37'])).
% 0.38/0.55  thf('39', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '40'])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.55  thf(redefinition_r3_orders_2, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.38/0.55         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.38/0.55          | ~ (l1_orders_2 @ X14)
% 0.38/0.55          | ~ (v3_orders_2 @ X14)
% 0.38/0.55          | (v2_struct_0 @ X14)
% 0.38/0.55          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.38/0.55          | (r1_orders_2 @ X14 @ X13 @ X15)
% 0.38/0.55          | ~ (r3_orders_2 @ X14 @ X13 @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.55          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.38/0.55          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.55  thf('46', plain, (![X38 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X38))),
% 0.38/0.55      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.38/0.55  thf('47', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.55          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X2 @ X0)
% 0.38/0.55          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.38/0.55  thf('49', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | ~ (m1_subset_1 @ 
% 0.38/0.55             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.38/0.55        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.55        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['41', '48'])).
% 0.38/0.55  thf('50', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | ~ (m1_subset_1 @ 
% 0.38/0.55             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.38/0.55        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.38/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.55        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '51'])).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.55           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.55        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.55         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.38/0.55          | ~ (r1_orders_2 @ X20 @ X19 @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55          | (zip_tseitin_0 @ 
% 0.38/0.55             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X0 @ 
% 0.38/0.55             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.55         ((zip_tseitin_1 @ X21 @ X22 @ X23 @ X24)
% 0.38/0.55          | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.55  thf('57', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55          | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55          | (zip_tseitin_1 @ 
% 0.38/0.55             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X0 @ 
% 0.38/0.55             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.55          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.38/0.55               X1 @ (k2_yellow_1 @ X0))
% 0.38/0.55          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.38/0.55      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.55        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '9'])).
% 0.38/0.55  thf('61', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.38/0.55  thf('63', plain,
% 0.38/0.55      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['62'])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.55         (((X27) = (k1_yellow_0 @ X25 @ X26))
% 0.38/0.55          | ~ (zip_tseitin_2 @ X26 @ X27 @ X25))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.55  thf('66', plain,
% 0.38/0.55      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.55        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['1', '65'])).
% 0.38/0.55  thf('67', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.55  thf('68', plain,
% 0.38/0.55      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.55        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.55  thf('69', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('70', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.38/0.55      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.38/0.55  thf(fc6_yellow_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.55       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.38/0.55         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.38/0.55  thf('71', plain,
% 0.38/0.55      (![X41 : $i]:
% 0.38/0.55         (~ (v2_struct_0 @ (k2_yellow_1 @ X41)) | (v1_xboole_0 @ X41))),
% 0.38/0.55      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.38/0.55  thf('72', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.38/0.55  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
