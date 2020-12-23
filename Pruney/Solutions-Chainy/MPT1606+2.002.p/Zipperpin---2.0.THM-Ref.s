%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDLmpktwz7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:11 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 302 expanded)
%              Number of leaves         :   47 ( 116 expanded)
%              Depth                    :   29
%              Number of atoms          : 1188 (3048 expanded)
%              Number of equality atoms :   22 ( 107 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(t14_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
         => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
            = ( k3_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k4_yellow_0 @ A )
        = ( k2_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( ( k4_yellow_0 @ X10 )
        = ( k2_yellow_0 @ X10 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d12_yellow_0])).

thf('2',plain,(
    r2_hidden @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( m1_subset_1 @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X36: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ( r1_lattice3 @ X28 @ k1_xboole_0 @ X27 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X36: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t31_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) )
                  & ( r1_lattice3 @ A @ C @ B ) )
               => ( ( r2_yellow_0 @ A @ C )
                  & ( B
                    = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X36: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k2_yellow_0 @ A @ C ) )
        & ( r2_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r1_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ D @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k2_yellow_0 @ A @ C ) )
                  & ( r2_yellow_0 @ A @ C ) )
               => ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_lattice3 @ X23 @ X26 @ X22 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X26 @ X22 @ X23 ) @ X26 @ X22 @ X23 )
      | ( zip_tseitin_2 @ X26 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X34: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('20',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('25',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('28',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('32',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('34',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ ( k2_yellow_1 @ X39 ) ) )
      | ~ ( r1_tarski @ X38 @ X40 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X39 ) @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ ( k2_yellow_1 @ X39 ) ) )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('35',plain,(
    ! [X36: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('36',plain,(
    ! [X36: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('37',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r1_tarski @ X38 @ X40 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X39 ) @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('41',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X36: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) )
      = X36 ) ),
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

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r3_orders_2 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X36: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('49',plain,(
    ! [X32: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('50',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('54',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( r1_orders_2 @ X14 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('62',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('64',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('65',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X21
        = ( k2_yellow_0 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X21 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( k3_tarski @ sk_A )
      = ( k2_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k3_tarski @ sk_A )
      = ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','68'])).

thf('70',plain,(
    ! [X30: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('71',plain,
    ( ( ( k3_tarski @ sk_A )
      = ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != ( k3_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('74',plain,(
    ! [X35: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X35 ) )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('75',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDLmpktwz7
% 0.15/0.38  % Computer   : n016.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 16:07:19 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 133 iterations in 0.108s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.39/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.39/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.61  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.39/0.61  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.39/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.39/0.61  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.61  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.39/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.61  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.39/0.61  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.39/0.61  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.61  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.39/0.61  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.39/0.61  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.39/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.39/0.61  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.39/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.39/0.61  thf(t14_yellow_1, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.39/0.61         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61          ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.39/0.61            ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t14_yellow_1])).
% 0.39/0.61  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d12_yellow_0, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( l1_orders_2 @ A ) =>
% 0.39/0.61       ( ( k4_yellow_0 @ A ) = ( k2_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X10 : $i]:
% 0.39/0.61         (((k4_yellow_0 @ X10) = (k2_yellow_0 @ X10 @ k1_xboole_0))
% 0.39/0.61          | ~ (l1_orders_2 @ X10))),
% 0.39/0.61      inference('cnf', [status(esa)], [d12_yellow_0])).
% 0.39/0.61  thf('2', plain, ((r2_hidden @ (k3_tarski @ sk_A) @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d2_subset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.39/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.39/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X2 @ X3)
% 0.39/0.61          | (m1_subset_1 @ X2 @ X3)
% 0.39/0.61          | (v1_xboole_0 @ X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (((v1_xboole_0 @ sk_A) | (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('6', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf(t1_yellow_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.39/0.61       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.61  thf('7', plain, (![X36 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X36)) = (X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.61  thf(t6_yellow_0, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( l1_orders_2 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.39/0.61             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X27 : $i, X28 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.39/0.61          | (r1_lattice3 @ X28 @ k1_xboole_0 @ X27)
% 0.39/0.61          | ~ (l1_orders_2 @ X28))),
% 0.39/0.61      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.61  thf(dt_k2_yellow_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.39/0.61       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.39/0.61  thf('10', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ (k3_tarski @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['6', '11'])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (![X36 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X36)) = (X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.61  thf(t31_yellow_0, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61           ( ![C:$i]:
% 0.39/0.61             ( ( ( ( r2_yellow_0 @ A @ C ) & 
% 0.39/0.61                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) =>
% 0.39/0.61                 ( ( ![D:$i]:
% 0.39/0.61                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.39/0.61                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 0.39/0.61                   ( r1_lattice3 @ A @ C @ B ) ) ) & 
% 0.39/0.61               ( ( ( ![D:$i]:
% 0.39/0.61                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.39/0.61                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 0.39/0.61                   ( r1_lattice3 @ A @ C @ B ) ) =>
% 0.39/0.61                 ( ( r2_yellow_0 @ A @ C ) & 
% 0.39/0.61                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_1, axiom,
% 0.39/0.61    (![D:$i,C:$i,B:$i,A:$i]:
% 0.39/0.61     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.39/0.61       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.61         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 0.39/0.61          | (m1_subset_1 @ X15 @ (u1_struct_0 @ X18)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.61         ((m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X36 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X36)) = (X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.61  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.39/0.61  thf(zf_stmt_3, axiom,
% 0.39/0.61    (![C:$i,B:$i,A:$i]:
% 0.39/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.39/0.61       ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & ( r2_yellow_0 @ A @ C ) ) ))).
% 0.39/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.39/0.61  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.39/0.61  thf(zf_stmt_6, axiom,
% 0.39/0.61    (![D:$i,C:$i,B:$i,A:$i]:
% 0.39/0.61     ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ D @ B ) ) =>
% 0.39/0.61       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.39/0.61  thf(zf_stmt_7, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61           ( ![C:$i]:
% 0.39/0.61             ( ( ( ( r1_lattice3 @ A @ C @ B ) & 
% 0.39/0.61                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.39/0.61                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.39/0.61               ( ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & 
% 0.39/0.61                   ( r2_yellow_0 @ A @ C ) ) =>
% 0.39/0.61                 ( ( r1_lattice3 @ A @ C @ B ) & 
% 0.39/0.61                   ( ![D:$i]:
% 0.39/0.61                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.39/0.61                         ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X22 : $i, X23 : $i, X26 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.39/0.61          | ~ (r1_lattice3 @ X23 @ X26 @ X22)
% 0.39/0.61          | ~ (zip_tseitin_1 @ (sk_D @ X26 @ X22 @ X23) @ X26 @ X22 @ X23)
% 0.39/0.61          | (zip_tseitin_2 @ X26 @ X22 @ X23)
% 0.39/0.61          | ~ (l1_orders_2 @ X23)
% 0.39/0.61          | ~ (v5_orders_2 @ X23))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.39/0.61               X1 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.61  thf(fc5_yellow_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.39/0.61       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.39/0.61       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.39/0.61       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.39/0.61  thf('19', plain, (![X34 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X34))),
% 0.39/0.61      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.39/0.61  thf('20', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.39/0.61               X1 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((m1_subset_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.39/0.61          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.39/0.61          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['15', '21'])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      ((~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (m1_subset_1 @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['12', '22'])).
% 0.39/0.61  thf('24', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (m1_subset_1 @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (m1_subset_1 @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X2 @ X3)
% 0.39/0.61          | (r2_hidden @ X2 @ X3)
% 0.39/0.61          | (v1_xboole_0 @ X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (v1_xboole_0 @ sk_A)
% 0.39/0.61        | (r2_hidden @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.61  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (((r2_hidden @ 
% 0.39/0.61         (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61         sk_A)
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['28', '29'])).
% 0.39/0.61  thf(l49_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_tarski @ X0 @ (k3_tarski @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (r1_tarski @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (m1_subset_1 @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.61  thf(t3_yellow_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.39/0.61           ( ![C:$i]:
% 0.39/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.39/0.61               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.39/0.61                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ (k2_yellow_1 @ X39)))
% 0.39/0.61          | ~ (r1_tarski @ X38 @ X40)
% 0.39/0.61          | (r3_orders_2 @ (k2_yellow_1 @ X39) @ X38 @ X40)
% 0.39/0.61          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ (k2_yellow_1 @ X39)))
% 0.39/0.61          | (v1_xboole_0 @ X39))),
% 0.39/0.61      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.39/0.61  thf('35', plain,
% 0.39/0.61      (![X36 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X36)) = (X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      (![X36 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X36)) = (X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X38 @ X39)
% 0.39/0.61          | ~ (r1_tarski @ X38 @ X40)
% 0.39/0.61          | (r3_orders_2 @ (k2_yellow_1 @ X39) @ X38 @ X40)
% 0.39/0.61          | ~ (m1_subset_1 @ X40 @ X39)
% 0.39/0.61          | (v1_xboole_0 @ X39))),
% 0.39/0.61      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A))
% 0.39/0.61          | (v1_xboole_0 @ sk_A)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.39/0.61          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61             X0)
% 0.39/0.61          | ~ (r1_tarski @ 
% 0.39/0.61               (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61               X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['33', '37'])).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A))
% 0.39/0.61        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.39/0.61        | (v1_xboole_0 @ sk_A)
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['32', '38'])).
% 0.39/0.61  thf('40', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A))
% 0.39/0.61        | (v1_xboole_0 @ sk_A)
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      (((v1_xboole_0 @ sk_A)
% 0.39/0.61        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A))
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.61  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('44', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A)))),
% 0.39/0.61      inference('clc', [status(thm)], ['42', '43'])).
% 0.39/0.61  thf('45', plain,
% 0.39/0.61      (![X36 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X36)) = (X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.61  thf(redefinition_r3_orders_2, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.61         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.39/0.61         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.39/0.61  thf('46', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.39/0.61          | ~ (l1_orders_2 @ X8)
% 0.39/0.61          | ~ (v3_orders_2 @ X8)
% 0.39/0.61          | (v2_struct_0 @ X8)
% 0.39/0.61          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.39/0.61          | (r1_orders_2 @ X8 @ X7 @ X9)
% 0.39/0.61          | ~ (r3_orders_2 @ X8 @ X7 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.39/0.61  thf('47', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.39/0.61          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.39/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.39/0.61          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.61  thf('48', plain,
% 0.39/0.61      (![X36 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X36)) = (X36))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.61  thf('49', plain, (![X32 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X32))),
% 0.39/0.61      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.39/0.61  thf('50', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.39/0.61  thf('51', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.39/0.61          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.39/0.61          | ~ (m1_subset_1 @ X2 @ X0)
% 0.39/0.61          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.39/0.61  thf('52', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.39/0.61        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A))
% 0.39/0.61        | ~ (m1_subset_1 @ 
% 0.39/0.61             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61             sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['44', '51'])).
% 0.39/0.61  thf('53', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('54', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A))
% 0.39/0.61        | ~ (m1_subset_1 @ 
% 0.39/0.61             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61             sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.61  thf('55', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A))
% 0.39/0.61        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['25', '54'])).
% 0.39/0.61  thf('56', plain,
% 0.39/0.61      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.39/0.61           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61           (k3_tarski @ sk_A))
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['55'])).
% 0.39/0.61  thf('57', plain,
% 0.39/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.61         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.39/0.61          | ~ (r1_orders_2 @ X14 @ X11 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.39/0.61  thf('58', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A))
% 0.39/0.61          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61          | (zip_tseitin_0 @ 
% 0.39/0.61             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61             X0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.39/0.61  thf('59', plain,
% 0.39/0.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.61         ((zip_tseitin_1 @ X15 @ X16 @ X17 @ X18)
% 0.39/0.61          | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.61  thf('60', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61             (k2_yellow_1 @ sk_A))
% 0.39/0.61          | (zip_tseitin_1 @ 
% 0.39/0.61             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.39/0.61             X0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.61  thf('61', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X1 @ X0)
% 0.39/0.61          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.39/0.61               X1 @ (k2_yellow_1 @ X0))
% 0.39/0.61          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.39/0.61  thf('62', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | ~ (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.39/0.61             (k3_tarski @ sk_A))
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A))
% 0.39/0.61        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.61  thf('63', plain,
% 0.39/0.61      ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ (k3_tarski @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['6', '11'])).
% 0.39/0.61  thf('64', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.39/0.61      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('65', plain,
% 0.39/0.61      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61         (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.39/0.61  thf('66', plain,
% 0.39/0.61      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.39/0.61           (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['65'])).
% 0.39/0.61  thf('67', plain,
% 0.39/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.61         (((X21) = (k2_yellow_0 @ X19 @ X20))
% 0.39/0.61          | ~ (zip_tseitin_2 @ X20 @ X21 @ X19))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.61  thf('68', plain,
% 0.39/0.61      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | ((k3_tarski @ sk_A)
% 0.39/0.61            = (k2_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.61  thf('69', plain,
% 0.39/0.61      ((((k3_tarski @ sk_A) = (k4_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.39/0.61        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.39/0.61        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['1', '68'])).
% 0.39/0.61  thf('70', plain, (![X30 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X30))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.39/0.61  thf('71', plain,
% 0.39/0.61      ((((k3_tarski @ sk_A) = (k4_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.39/0.61        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['69', '70'])).
% 0.39/0.61  thf('72', plain,
% 0.39/0.61      (((k4_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k3_tarski @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('73', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.39/0.61      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.39/0.61  thf(fc6_yellow_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.39/0.61         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.39/0.61  thf('74', plain,
% 0.39/0.61      (![X35 : $i]:
% 0.39/0.61         (~ (v2_struct_0 @ (k2_yellow_1 @ X35)) | (v1_xboole_0 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.39/0.61  thf('75', plain, ((v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.61  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
