%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01FfzZPvaW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 245 expanded)
%              Number of leaves         :   46 (  98 expanded)
%              Depth                    :   23
%              Number of atoms          :  984 (2217 expanded)
%              Number of equality atoms :   22 (  87 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

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
    ! [X7: $i] :
      ( ( ( k3_yellow_0 @ X7 )
        = ( k1_yellow_0 @ X7 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('2',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
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
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( m1_subset_1 @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( r2_lattice3 @ X25 @ k1_xboole_0 @ X24 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
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

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
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

thf('17',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_lattice3 @ X20 @ X23 @ X19 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 )
      | ( zip_tseitin_2 @ X23 @ X19 @ X20 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X31: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('20',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('25',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('27',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ~ ( r1_tarski @ X35 @ X37 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ ( k2_yellow_1 @ X36 ) ) )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('29',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('30',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('31',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ~ ( r1_tarski @ X35 @ X37 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X36 ) @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
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

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r3_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X33: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('42',plain,(
    ! [X29: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('43',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('47',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ X10 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_1 @ X12 @ X13 @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('55',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','11'])).

thf('57',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['4','5'])).

thf('58',plain,
    ( ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k1_yellow_0 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','61'])).

thf('63',plain,(
    ! [X27: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X32: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X32 ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('68',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01FfzZPvaW
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 178 iterations in 0.124s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.58  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.58  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.58  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.21/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.58  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.58  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.58  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.58  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.58  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.58  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.58  thf(t13_yellow_1, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.58       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.58         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.58          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.58            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.21/0.58  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(d11_yellow_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_orders_2 @ A ) =>
% 0.21/0.58       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X7 : $i]:
% 0.21/0.58         (((k3_yellow_0 @ X7) = (k1_yellow_0 @ X7 @ k1_xboole_0))
% 0.21/0.58          | ~ (l1_orders_2 @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.21/0.58  thf('2', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(d2_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X1 @ X2)
% 0.21/0.58          | (m1_subset_1 @ X1 @ X2)
% 0.21/0.58          | (v1_xboole_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (((v1_xboole_0 @ sk_A) | (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.58  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('6', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf(t1_yellow_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.58       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.58  thf('7', plain, (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.58  thf(t6_yellow_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_orders_2 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.21/0.58             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.21/0.58          | (r2_lattice3 @ X25 @ k1_xboole_0 @ X24)
% 0.21/0.58          | ~ (l1_orders_2 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf(dt_k2_yellow_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.58       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.58  thf('10', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.58  thf(t30_yellow_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.21/0.58                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.21/0.58                 ( ( ![D:$i]:
% 0.21/0.58                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.58                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.21/0.58                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.21/0.58               ( ( ( ![D:$i]:
% 0.21/0.58                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.58                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.21/0.58                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.21/0.58                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.21/0.58                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_1, axiom,
% 0.21/0.58    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.58     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.21/0.58       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.58          | (m1_subset_1 @ X12 @ (u1_struct_0 @ X15)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.58         ((m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.58  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_3, axiom,
% 0.21/0.58    (![C:$i,B:$i,A:$i]:
% 0.21/0.58     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.21/0.58       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.21/0.58  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_6, axiom,
% 0.21/0.58    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.58     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.21/0.58       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.21/0.58  thf(zf_stmt_7, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.21/0.58                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.21/0.58                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.21/0.58               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.21/0.58                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.21/0.58                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.21/0.58                   ( ![D:$i]:
% 0.21/0.58                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.58                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.21/0.58          | ~ (r2_lattice3 @ X20 @ X23 @ X19)
% 0.21/0.58          | ~ (zip_tseitin_1 @ (sk_D @ X23 @ X19 @ X20) @ X23 @ X19 @ X20)
% 0.21/0.58          | (zip_tseitin_2 @ X23 @ X19 @ X20)
% 0.21/0.58          | ~ (l1_orders_2 @ X20)
% 0.21/0.58          | ~ (v5_orders_2 @ X20))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.21/0.58               X1 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf(fc5_yellow_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.58       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.58       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.58       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.58  thf('19', plain, (![X31 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X31))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.58  thf('20', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.21/0.58               X1 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((m1_subset_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.58          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.58          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['15', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      ((~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.58        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (m1_subset_1 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '22'])).
% 0.21/0.58  thf('24', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (m1_subset_1 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (m1_subset_1 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.58  thf('27', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf(t3_yellow_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.58               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.21/0.58                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.21/0.58          | ~ (r1_tarski @ X35 @ X37)
% 0.21/0.58          | (r3_orders_2 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.21/0.58          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ (k2_yellow_1 @ X36)))
% 0.21/0.58          | (v1_xboole_0 @ X36))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X35 @ X36)
% 0.21/0.58          | ~ (r1_tarski @ X35 @ X37)
% 0.21/0.58          | (r3_orders_2 @ (k2_yellow_1 @ X36) @ X35 @ X37)
% 0.21/0.58          | ~ (m1_subset_1 @ X37 @ X36)
% 0.21/0.58          | (v1_xboole_0 @ X36))),
% 0.21/0.58      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.58          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.21/0.58          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['27', '31'])).
% 0.21/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.58  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.58          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.58  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.21/0.58      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['26', '36'])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.58  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.58         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.58         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.58          | ~ (l1_orders_2 @ X5)
% 0.21/0.58          | ~ (v3_orders_2 @ X5)
% 0.21/0.58          | (v2_struct_0 @ X5)
% 0.21/0.58          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.21/0.58          | (r1_orders_2 @ X5 @ X4 @ X6)
% 0.21/0.58          | ~ (r3_orders_2 @ X5 @ X4 @ X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.58          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.58          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X33 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X33)) = (X33))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.58  thf('42', plain, (![X29 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X29))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.58  thf('43', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.58          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.58          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.58          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | ~ (m1_subset_1 @ 
% 0.21/0.58             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.21/0.58        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.58        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['37', '44'])).
% 0.21/0.58  thf('46', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | ~ (m1_subset_1 @ 
% 0.21/0.58             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.21/0.58        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.58        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '47'])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.21/0.58           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.58        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.58         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.58          | ~ (r1_orders_2 @ X11 @ X10 @ X8))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58          | (zip_tseitin_0 @ 
% 0.21/0.58             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X0 @ 
% 0.21/0.58             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         ((zip_tseitin_1 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.58          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58          | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58          | (zip_tseitin_1 @ 
% 0.21/0.58             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X0 @ 
% 0.21/0.58             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.58          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (zip_tseitin_1 @ (sk_D @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.21/0.58               X1 @ (k2_yellow_1 @ X0))
% 0.21/0.58          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.58        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.58  thf('57', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      (((zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.58         (((X18) = (k1_yellow_0 @ X16 @ X17))
% 0.21/0.58          | ~ (zip_tseitin_2 @ X17 @ X18 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.58        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.21/0.58        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['1', '61'])).
% 0.21/0.58  thf('63', plain, (![X27 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X27))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.58        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.58  thf('65', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('66', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.21/0.58  thf(fc6_yellow_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.21/0.58         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      (![X32 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k2_yellow_1 @ X32)) | (v1_xboole_0 @ X32))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.21/0.58  thf('68', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.58  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.43/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
