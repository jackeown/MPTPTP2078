%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kcG9u5A2yg

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 241 expanded)
%              Number of leaves         :   49 ( 100 expanded)
%              Depth                    :   24
%              Number of atoms          : 1065 (2170 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

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
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ X14 )
        = ( k1_yellow_0 @ X14 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('3',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('5',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X32: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
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

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_1 @ X19 @ X20 @ X21 @ X22 )
      | ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
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

thf('19',plain,(
    ! [X26: $i,X27: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_lattice3 @ X27 @ X30 @ X26 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X30 @ X26 @ X27 ) @ X30 @ X26 @ X27 )
      | ( zip_tseitin_2 @ X30 @ X26 @ X27 )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v5_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X36: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('22',plain,(
    ! [X32: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('29',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('30',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ ( k2_yellow_1 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X40 ) @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ ( k2_yellow_1 @ X40 ) ) )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('31',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('32',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('33',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ X40 )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X40 ) @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
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

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r3_orders_2 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X34: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('45',plain,(
    ! [X32: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('49',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( r1_orders_2 @ X18 @ X17 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_1 @ X19 @ X20 @ X21 @ X22 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('57',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','13'])).

thf('59',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('60',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X25
        = ( k1_yellow_0 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_2 @ X24 @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','63'])).

thf('65',plain,(
    ! [X32: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('66',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ~ ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X32: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('73',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('74',plain,(
    ! [X0: $i] :
      ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kcG9u5A2yg
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 104 iterations in 0.074s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.52  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.19/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.19/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.19/0.52  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.19/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.52  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.19/0.52  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.19/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.52  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.19/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.52  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.19/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.52  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.52  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.19/0.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.52  thf(t13_yellow_1, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.52       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.19/0.52         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.52          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.19/0.52            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.19/0.52  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d11_yellow_0, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_orders_2 @ A ) =>
% 0.19/0.52       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X14 : $i]:
% 0.19/0.52         (((k3_yellow_0 @ X14) = (k1_yellow_0 @ X14 @ k1_xboole_0))
% 0.19/0.52          | ~ (l1_orders_2 @ X14))),
% 0.19/0.52      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.19/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.52  thf('2', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.52  thf('3', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t1_subset, axiom,
% 0.19/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.52  thf('4', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.53  thf('5', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf(t1_yellow_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.19/0.53       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.53  thf('6', plain, (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf(d9_lattice3, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_orders_2 @ A ) =>
% 0.19/0.53       ( ![B:$i,C:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.19/0.53             ( ![D:$i]:
% 0.19/0.53               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.19/0.53          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 0.19/0.53          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.19/0.53          | ~ (l1_orders_2 @ X11))),
% 0.19/0.53      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.19/0.53          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.19/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.53  thf(dt_k2_yellow_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.19/0.53       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.19/0.53  thf('9', plain, (![X32 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X32))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.19/0.53          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.19/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.19/0.53          | (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.19/0.53  thf(t7_ordinal1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X3 : $i, X4 : $i]: (~ (r2_hidden @ X3 @ X4) | ~ (r1_tarski @ X4 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.19/0.53          | ~ (r1_tarski @ X0 @ 
% 0.19/0.53               (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '13'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf(t30_yellow_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.19/0.53                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.19/0.53                 ( ( ![D:$i]:
% 0.19/0.53                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.19/0.53                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.19/0.53                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.19/0.53               ( ( ( ![D:$i]:
% 0.19/0.53                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.19/0.53                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.19/0.53                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.19/0.53                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.19/0.53                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_1, axiom,
% 0.19/0.53    (![D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.53     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.19/0.53       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.53         ((zip_tseitin_1 @ X19 @ X20 @ X21 @ X22)
% 0.19/0.53          | (m1_subset_1 @ X19 @ (u1_struct_0 @ X22)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         ((m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_3, axiom,
% 0.19/0.53    (![C:$i,B:$i,A:$i]:
% 0.19/0.53     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.19/0.53       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.19/0.53  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.53  thf(zf_stmt_6, axiom,
% 0.19/0.53    (![D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.53     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.19/0.53       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.19/0.53  thf(zf_stmt_7, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.19/0.53                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.19/0.53                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.19/0.53               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.19/0.53                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.19/0.53                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.19/0.53                   ( ![D:$i]:
% 0.19/0.53                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.19/0.53                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X26 : $i, X27 : $i, X30 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.19/0.53          | ~ (r2_lattice3 @ X27 @ X30 @ X26)
% 0.19/0.53          | ~ (zip_tseitin_1 @ (sk_D_1 @ X30 @ X26 @ X27) @ X30 @ X26 @ X27)
% 0.19/0.53          | (zip_tseitin_2 @ X30 @ X26 @ X27)
% 0.19/0.53          | ~ (l1_orders_2 @ X27)
% 0.19/0.53          | ~ (v5_orders_2 @ X27))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (zip_tseitin_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.19/0.53               X1 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf(fc5_yellow_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.19/0.53       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.19/0.53       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.19/0.53       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.19/0.53  thf('21', plain, (![X36 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X36))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.19/0.53  thf('22', plain, (![X32 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X32))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (zip_tseitin_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.19/0.53               X1 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.19/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.19/0.53          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.19/0.53          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['17', '23'])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      ((~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.19/0.53        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (m1_subset_1 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['14', '24'])).
% 0.19/0.53  thf('26', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (m1_subset_1 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (m1_subset_1 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.53  thf('29', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf(t3_yellow_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.19/0.53               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.19/0.53                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X39 @ (u1_struct_0 @ (k2_yellow_1 @ X40)))
% 0.19/0.53          | ~ (r1_tarski @ X39 @ X41)
% 0.19/0.53          | (r3_orders_2 @ (k2_yellow_1 @ X40) @ X39 @ X41)
% 0.19/0.53          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ (k2_yellow_1 @ X40)))
% 0.19/0.53          | (v1_xboole_0 @ X40))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X39 @ X40)
% 0.19/0.53          | ~ (r1_tarski @ X39 @ X41)
% 0.19/0.53          | (r3_orders_2 @ (k2_yellow_1 @ X40) @ X39 @ X41)
% 0.19/0.53          | ~ (m1_subset_1 @ X41 @ X40)
% 0.19/0.53          | (v1_xboole_0 @ X40))),
% 0.19/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ sk_A)
% 0.19/0.53          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.53          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.19/0.53          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['29', '33'])).
% 0.19/0.53  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ sk_A)
% 0.19/0.53          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.53          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.53  thf('37', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.19/0.53          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.19/0.53      inference('clc', [status(thm)], ['36', '37'])).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['28', '38'])).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf(redefinition_r3_orders_2, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.53         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.53       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.19/0.53          | ~ (l1_orders_2 @ X8)
% 0.19/0.53          | ~ (v3_orders_2 @ X8)
% 0.19/0.53          | (v2_struct_0 @ X8)
% 0.19/0.53          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.19/0.53          | (r1_orders_2 @ X8 @ X7 @ X9)
% 0.19/0.53          | ~ (r3_orders_2 @ X8 @ X7 @ X9))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.19/0.53          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.19/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.19/0.53          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf('44', plain, (![X34 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X34))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.19/0.53  thf('45', plain, (![X32 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X32))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.19/0.53          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.19/0.53          | ~ (m1_subset_1 @ X2 @ X0)
% 0.19/0.53          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | ~ (m1_subset_1 @ 
% 0.19/0.53             (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.19/0.53        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.19/0.53        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['39', '46'])).
% 0.19/0.53  thf('48', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | ~ (m1_subset_1 @ 
% 0.19/0.53             (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.19/0.53        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.19/0.53      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.53  thf('50', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.19/0.53        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['27', '49'])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.19/0.53           (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.19/0.53        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.19/0.53  thf('52', plain,
% 0.19/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.53         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.19/0.53          | ~ (r1_orders_2 @ X18 @ X17 @ X15))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53          | (zip_tseitin_0 @ 
% 0.19/0.53             (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.19/0.53             X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.53  thf('54', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.53         ((zip_tseitin_1 @ X19 @ X20 @ X21 @ X22)
% 0.19/0.53          | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.53  thf('55', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53          | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53          | (zip_tseitin_1 @ 
% 0.19/0.53             (sk_D_1 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.19/0.53             X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.53  thf('56', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.19/0.53          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (zip_tseitin_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.19/0.53               X1 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.19/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.53  thf('57', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)
% 0.19/0.53        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '13'])).
% 0.19/0.53  thf('59', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.19/0.53  thf('61', plain,
% 0.19/0.53      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.19/0.53  thf('62', plain,
% 0.19/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.53         (((X25) = (k1_yellow_0 @ X23 @ X24))
% 0.19/0.53          | ~ (zip_tseitin_2 @ X24 @ X25 @ X23))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.53  thf('63', plain,
% 0.19/0.53      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.19/0.53  thf('64', plain,
% 0.19/0.53      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.19/0.53        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.19/0.53        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['1', '63'])).
% 0.19/0.53  thf('65', plain, (![X32 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X32))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.19/0.53  thf('66', plain,
% 0.19/0.53      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.19/0.53        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.19/0.53      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.53  thf('67', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('68', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.19/0.53      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.19/0.53  thf('69', plain,
% 0.19/0.53      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.19/0.53  thf(fc1_struct_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.53       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.19/0.53  thf('70', plain,
% 0.19/0.53      (![X5 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.19/0.53          | ~ (l1_struct_0 @ X5)
% 0.19/0.53          | ~ (v2_struct_0 @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.19/0.53  thf('71', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X0)
% 0.19/0.53          | ~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.19/0.53          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['69', '70'])).
% 0.19/0.53  thf('72', plain, (![X32 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X32))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.19/0.53  thf(dt_l1_orders_2, axiom,
% 0.19/0.53    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.53  thf('73', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.19/0.53  thf('74', plain, (![X0 : $i]: (l1_struct_0 @ (k2_yellow_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.19/0.53  thf('75', plain,
% 0.19/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['71', '74'])).
% 0.19/0.53  thf('76', plain, ((v1_xboole_0 @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['68', '75'])).
% 0.19/0.53  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
