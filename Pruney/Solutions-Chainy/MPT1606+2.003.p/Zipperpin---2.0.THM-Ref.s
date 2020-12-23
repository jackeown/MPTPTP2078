%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FDoDsBAa6p

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 265 expanded)
%              Number of leaves         :   48 ( 107 expanded)
%              Depth                    :   28
%              Number of atoms          : 1293 (2644 expanded)
%              Number of equality atoms :   24 (  90 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

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

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X9: $i] :
      ( ( ( k4_yellow_0 @ X9 )
        = ( k2_yellow_0 @ X9 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_yellow_0])).

thf('2',plain,(
    r2_hidden @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( r1_lattice3 @ X27 @ k1_xboole_0 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X29: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
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

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
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

thf('15',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_lattice3 @ X22 @ X25 @ X21 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X25 @ X21 @ X22 ) @ X25 @ X21 @ X22 )
      | ( zip_tseitin_2 @ X25 @ X21 @ X22 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X33: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('18',plain,(
    ! [X29: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('23',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('25',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('36',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('40',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('42',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ ( k2_yellow_1 @ X38 ) ) )
      | ~ ( r1_tarski @ X37 @ X39 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X38 ) @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ ( k2_yellow_1 @ X38 ) ) )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('43',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('45',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ X38 )
      | ~ ( r1_tarski @ X37 @ X39 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X38 ) @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('49',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
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

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( r1_orders_2 @ X7 @ X6 @ X8 )
      | ~ ( r3_orders_2 @ X7 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X35: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('57',plain,(
    ! [X31: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('58',plain,(
    ! [X29: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X13 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_1 @ X14 @ X15 @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('70',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('72',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('73',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X20
        = ( k2_yellow_0 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X20 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( k3_tarski @ sk_A )
      = ( k2_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k3_tarski @ sk_A )
      = ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','76'])).

thf('78',plain,(
    ! [X29: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('79',plain,
    ( ( ( k3_tarski @ sk_A )
      = ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != ( k3_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('82',plain,(
    ! [X34: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X34 ) )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('83',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FDoDsBAa6p
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 123 iterations in 0.069s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.20/0.54  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.54  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.54  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.54  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.20/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.54  thf(t14_yellow_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.20/0.54         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54          ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.20/0.54            ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t14_yellow_1])).
% 0.20/0.54  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d12_yellow_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ A ) =>
% 0.20/0.54       ( ( k4_yellow_0 @ A ) = ( k2_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X9 : $i]:
% 0.20/0.54         (((k4_yellow_0 @ X9) = (k2_yellow_0 @ X9 @ k1_xboole_0))
% 0.20/0.54          | ~ (l1_orders_2 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [d12_yellow_0])).
% 0.20/0.54  thf('2', plain, ((r2_hidden @ (k3_tarski @ sk_A) @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t1_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.54  thf('4', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(t1_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.54       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.54  thf('5', plain, (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(t6_yellow_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.20/0.54             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.20/0.54          | (r1_lattice3 @ X27 @ k1_xboole_0 @ X26)
% 0.20/0.54          | ~ (l1_orders_2 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf(dt_k2_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.54  thf('8', plain, (![X29 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ (k3_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(t31_yellow_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( ( r2_yellow_0 @ A @ C ) & 
% 0.20/0.54                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) =>
% 0.20/0.54                 ( ( ![D:$i]:
% 0.20/0.54                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.20/0.54                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 0.20/0.54                   ( r1_lattice3 @ A @ C @ B ) ) ) & 
% 0.20/0.54               ( ( ( ![D:$i]:
% 0.20/0.54                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.20/0.54                         ( r1_orders_2 @ A @ D @ B ) ) ) ) & 
% 0.20/0.54                   ( r1_lattice3 @ A @ C @ B ) ) =>
% 0.20/0.54                 ( ( r2_yellow_0 @ A @ C ) & 
% 0.20/0.54                   ( ( B ) = ( k2_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, axiom,
% 0.20/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.20/0.54       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((zip_tseitin_1 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.54          | (m1_subset_1 @ X14 @ (u1_struct_0 @ X17)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_3, axiom,
% 0.20/0.54    (![C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.20/0.54       ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & ( r2_yellow_0 @ A @ C ) ) ))).
% 0.20/0.54  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_6, axiom,
% 0.20/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ D @ B ) ) =>
% 0.20/0.54       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.20/0.54  thf(zf_stmt_7, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( ( r1_lattice3 @ A @ C @ B ) & 
% 0.20/0.54                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.20/0.54                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.20/0.54               ( ( ( ( B ) = ( k2_yellow_0 @ A @ C ) ) & 
% 0.20/0.54                   ( r2_yellow_0 @ A @ C ) ) =>
% 0.20/0.54                 ( ( r1_lattice3 @ A @ C @ B ) & 
% 0.20/0.54                   ( ![D:$i]:
% 0.20/0.54                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                       ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.20/0.54                         ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i, X25 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.20/0.54          | ~ (r1_lattice3 @ X22 @ X25 @ X21)
% 0.20/0.54          | ~ (zip_tseitin_1 @ (sk_D @ X25 @ X21 @ X22) @ X25 @ X21 @ X22)
% 0.20/0.54          | (zip_tseitin_2 @ X25 @ X21 @ X22)
% 0.20/0.54          | ~ (l1_orders_2 @ X22)
% 0.20/0.54          | ~ (v5_orders_2 @ X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.20/0.54               X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf(fc5_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.54       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.54  thf('17', plain, (![X33 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X33))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.54  thf('18', plain, (![X29 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.20/0.54               X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((m1_subset_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.20/0.54          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.54          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '20'])).
% 0.20/0.54  thf('22', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ (k3_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((zip_tseitin_1 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.54          | (m1_subset_1 @ X14 @ (u1_struct_0 @ X17)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf(t2_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]:
% 0.20/0.54         ((r2_hidden @ X4 @ X5)
% 0.20/0.54          | (v1_xboole_0 @ X5)
% 0.20/0.54          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.54          | (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X0)
% 0.20/0.54          | (r2_hidden @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.20/0.54          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['25', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X0)
% 0.20/0.54          | (r2_hidden @ X1 @ X0)
% 0.20/0.54          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.20/0.54               X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.20/0.54          | (v1_xboole_0 @ X0)
% 0.20/0.54          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.20/0.54          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '33'])).
% 0.20/0.54  thf('35', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('37', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (((r2_hidden @ 
% 0.20/0.54         (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54         sk_A)
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf(l49_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r1_tarski @ X0 @ (k3_tarski @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_tarski @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (m1_subset_1 @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf(t3_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.20/0.54               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.20/0.54                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ (k2_yellow_1 @ X38)))
% 0.20/0.54          | ~ (r1_tarski @ X37 @ X39)
% 0.20/0.54          | (r3_orders_2 @ (k2_yellow_1 @ X38) @ X37 @ X39)
% 0.20/0.54          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ (k2_yellow_1 @ X38)))
% 0.20/0.54          | (v1_xboole_0 @ X38))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X37 @ X38)
% 0.20/0.54          | ~ (r1_tarski @ X37 @ X39)
% 0.20/0.54          | (r3_orders_2 @ (k2_yellow_1 @ X38) @ X37 @ X39)
% 0.20/0.54          | ~ (m1_subset_1 @ X39 @ X38)
% 0.20/0.54          | (v1_xboole_0 @ X38))),
% 0.20/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A))
% 0.20/0.54          | (v1_xboole_0 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.54          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54             X0)
% 0.20/0.54          | ~ (r1_tarski @ 
% 0.20/0.54               (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54               X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ sk_A)
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['40', '46'])).
% 0.20/0.54  thf('48', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A))
% 0.20/0.54        | (v1_xboole_0 @ sk_A)
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A))
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.54  thf('51', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf(redefinition_r3_orders_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.54         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.54          | ~ (l1_orders_2 @ X7)
% 0.20/0.54          | ~ (v3_orders_2 @ X7)
% 0.20/0.54          | (v2_struct_0 @ X7)
% 0.20/0.54          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.54          | (r1_orders_2 @ X7 @ X6 @ X8)
% 0.20/0.54          | ~ (r3_orders_2 @ X7 @ X6 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.20/0.54          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (![X35 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X35)) = (X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.54  thf('57', plain, (![X31 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.20/0.54  thf('58', plain, (![X29 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ X0)
% 0.20/0.54          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54             sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '59'])).
% 0.20/0.54  thf('61', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54             sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '62'])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.20/0.54           (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54           (k3_tarski @ sk_A))
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.54          | ~ (r1_orders_2 @ X13 @ X10 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A))
% 0.20/0.54          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54          | (zip_tseitin_0 @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54             X0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((zip_tseitin_1 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.54          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54          | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54             (k2_yellow_1 @ sk_A))
% 0.20/0.54          | (zip_tseitin_1 @ 
% 0.20/0.54             (sk_D @ k1_xboole_0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)) @ 
% 0.20/0.54             X0 @ (k3_tarski @ sk_A) @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.54          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.20/0.54               X1 @ (k2_yellow_1 @ X0))
% 0.20/0.54          | ~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.20/0.54             (k3_tarski @ sk_A))
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ~ (m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ (k3_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.54  thf('72', plain, ((m1_subset_1 @ (k3_tarski @ sk_A) @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (((zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54         (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (zip_tseitin_2 @ k1_xboole_0 @ (k3_tarski @ sk_A) @ 
% 0.20/0.54           (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         (((X20) = (k2_yellow_0 @ X18 @ X19))
% 0.20/0.54          | ~ (zip_tseitin_2 @ X19 @ X20 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | ((k3_tarski @ sk_A)
% 0.20/0.54            = (k2_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      ((((k3_tarski @ sk_A) = (k4_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '76'])).
% 0.20/0.54  thf('78', plain, (![X29 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      ((((k3_tarski @ sk_A) = (k4_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.20/0.54        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      (((k4_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k3_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('81', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.20/0.54  thf(fc6_yellow_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.20/0.54         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (![X34 : $i]:
% 0.20/0.54         (~ (v2_struct_0 @ (k2_yellow_1 @ X34)) | (v1_xboole_0 @ X34))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.20/0.54  thf('83', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.54      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.54  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
