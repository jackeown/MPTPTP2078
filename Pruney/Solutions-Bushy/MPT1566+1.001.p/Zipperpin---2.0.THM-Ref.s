%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1566+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pb964DStav

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  83 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  474 ( 814 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(t44_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_yellow_0])).

thf('0',plain,(
    ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ X0 )
        = ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( r1_yellow_0 @ X19 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v1_yellow_0 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_lattice3 @ X21 @ k1_xboole_0 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('5',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( u1_struct_0 @ X1 ) ) ) ),
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

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( X14
       != ( k1_yellow_0 @ X15 @ X16 ) )
      | ~ ( r1_yellow_0 @ X15 @ X16 )
      | ~ ( r2_lattice3 @ X15 @ X16 @ X17 )
      | ( r1_orders_2 @ X15 @ X14 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ ( k1_yellow_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r2_lattice3 @ X15 @ X16 @ X17 )
      | ~ ( r1_yellow_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( v5_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).


%------------------------------------------------------------------------------
