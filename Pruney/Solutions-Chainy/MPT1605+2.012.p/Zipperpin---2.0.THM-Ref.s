%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H4zHaVtmLE

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 213 expanded)
%              Number of leaves         :   46 (  90 expanded)
%              Depth                    :   22
%              Number of atoms          :  966 (1913 expanded)
%              Number of equality atoms :   22 (  71 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X6: $i] :
      ( ( ( k3_yellow_0 @ X6 )
        = ( k1_yellow_0 @ X6 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('2',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
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
    ! [X32: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r2_lattice3 @ X24 @ k1_xboole_0 @ X23 )
      | ~ ( l1_orders_2 @ X24 ) ) ),
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
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
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
    ! [X32: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) )
      = X32 ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X11 @ X12 @ X13 @ X14 )
      | ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X32: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) )
      = X32 ) ),
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
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_lattice3 @ X19 @ X22 @ X18 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 )
      | ( zip_tseitin_2 @ X22 @ X18 @ X19 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 ) ) ),
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
    ! [X30: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('18',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) ) )
      | ~ ( r1_tarski @ X34 @ X36 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X35 ) @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ ( k2_yellow_1 @ X35 ) ) )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('27',plain,(
    ! [X32: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('28',plain,(
    ! [X32: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('29',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ~ ( r1_tarski @ X34 @ X36 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X35 ) @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X32: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) )
      = X32 ) ),
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

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r3_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X32: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('40',plain,(
    ! [X28: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('41',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('45',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ~ ( r1_orders_2 @ X10 @ X9 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_1 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('53',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('55',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('56',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X17
        = ( k1_yellow_0 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_2 @ X16 @ X17 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','59'])).

thf('61',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('62',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X31: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X31 ) )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('66',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H4zHaVtmLE
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:49:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 79 iterations in 0.057s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.51  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.51  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.51  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.51  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.21/0.51  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(t13_yellow_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.51         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.51            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.21/0.51  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d11_yellow_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X6 : $i]:
% 0.21/0.51         (((k3_yellow_0 @ X6) = (k1_yellow_0 @ X6 @ k1_xboole_0))
% 0.21/0.51          | ~ (l1_orders_2 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.21/0.51  thf('2', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t1_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.51  thf('4', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(t1_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.51       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('5', plain, (![X32 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf(t6_yellow_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.21/0.51             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.21/0.51          | (r2_lattice3 @ X24 @ k1_xboole_0 @ X23)
% 0.21/0.51          | ~ (l1_orders_2 @ X24))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf(dt_k2_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.51       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.51  thf('8', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X32 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf(t30_yellow_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.21/0.51                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.21/0.51                 ( ( ![D:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.51                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.21/0.51                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.21/0.51               ( ( ( ![D:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.51                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.21/0.51                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.21/0.51                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.21/0.51                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, axiom,
% 0.21/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.21/0.51       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         ((zip_tseitin_1 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.51          | (m1_subset_1 @ X11 @ (u1_struct_0 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X32 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_3, axiom,
% 0.21/0.51    (![C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.21/0.51       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.21/0.51  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_6, axiom,
% 0.21/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.21/0.51       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.21/0.51  thf(zf_stmt_7, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.21/0.51                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.21/0.51                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.21/0.51               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.51                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.21/0.51                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.21/0.51                   ( ![D:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.51                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.51          | ~ (r2_lattice3 @ X19 @ X22 @ X18)
% 0.21/0.51          | ~ (zip_tseitin_1 @ (sk_D @ X22 @ X18 @ X19) @ X22 @ X18 @ X19)
% 0.21/0.51          | (zip_tseitin_2 @ X22 @ X18 @ X19)
% 0.21/0.51          | ~ (l1_orders_2 @ X19)
% 0.21/0.51          | ~ (v5_orders_2 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.21/0.51               X1 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf(fc5_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.51       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.51       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.51       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.51  thf('17', plain, (![X30 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.51  thf('18', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.21/0.51               X1 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.51          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.51          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.51        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '20'])).
% 0.21/0.51  thf('22', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('25', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(t3_yellow_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.51               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.21/0.51                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ (k2_yellow_1 @ X35)))
% 0.21/0.51          | ~ (r1_tarski @ X34 @ X36)
% 0.21/0.51          | (r3_orders_2 @ (k2_yellow_1 @ X35) @ X34 @ X36)
% 0.21/0.51          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ (k2_yellow_1 @ X35)))
% 0.21/0.51          | (v1_xboole_0 @ X35))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X32 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X32 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X34 @ X35)
% 0.21/0.51          | ~ (r1_tarski @ X34 @ X36)
% 0.21/0.51          | (r3_orders_2 @ (k2_yellow_1 @ X35) @ X34 @ X36)
% 0.21/0.51          | ~ (m1_subset_1 @ X36 @ X35)
% 0.21/0.51          | (v1_xboole_0 @ X35))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.51          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.21/0.51          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '29'])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.51          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X32 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.51          | ~ (l1_orders_2 @ X4)
% 0.21/0.51          | ~ (v3_orders_2 @ X4)
% 0.21/0.51          | (v2_struct_0 @ X4)
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.51          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.21/0.51          | ~ (r3_orders_2 @ X4 @ X3 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.51          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X32 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X32)) = (X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.51  thf('40', plain, (![X28 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.51  thf('41', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.51          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.51          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | ~ (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.21/0.51        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.51        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '42'])).
% 0.21/0.51  thf('44', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | ~ (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.21/0.51        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.51        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.51           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.51        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.51          | ~ (r1_orders_2 @ X10 @ X9 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51          | (zip_tseitin_0 @ 
% 0.21/0.51             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X0 @ 
% 0.21/0.51             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         ((zip_tseitin_1 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.51          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51          | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51          | (zip_tseitin_1 @ 
% 0.21/0.51             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X0 @ 
% 0.21/0.51             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.51          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.21/0.51               X1 @ (k2_yellow_1 @ X0))
% 0.21/0.51          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.51        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.51  thf('55', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         (((X17) = (k1_yellow_0 @ X15 @ X16))
% 0.21/0.51          | ~ (zip_tseitin_2 @ X16 @ X17 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.51        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '59'])).
% 0.21/0.51  thf('61', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.52        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf(fc6_yellow_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.21/0.52         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X31 : $i]:
% 0.21/0.52         (~ (v2_struct_0 @ (k2_yellow_1 @ X31)) | (v1_xboole_0 @ X31))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.21/0.52  thf('66', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.52  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.37/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
