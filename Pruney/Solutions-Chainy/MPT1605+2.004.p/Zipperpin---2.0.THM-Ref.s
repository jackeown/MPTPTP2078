%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7WS45fVx9y

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:09 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 226 expanded)
%              Number of leaves         :   48 (  94 expanded)
%              Depth                    :   25
%              Number of atoms          : 1087 (2136 expanded)
%              Number of equality atoms :   22 (  71 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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
    ! [X13: $i] :
      ( ( ( k3_yellow_0 @ X13 )
        = ( k1_yellow_0 @ X13 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('2',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
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

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X11 @ X10 ) @ X11 )
      | ( r2_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X31: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X18 @ X19 @ X20 @ X21 )
      | ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_lattice3 @ X26 @ X29 @ X25 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X29 @ X25 @ X26 ) @ X29 @ X25 @ X26 )
      | ( zip_tseitin_2 @ X29 @ X25 @ X26 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X35: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('21',plain,(
    ! [X31: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ ( k2_yellow_1 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X40 ) @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ ( k2_yellow_1 @ X40 ) ) )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('30',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('31',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('32',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ X40 )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X40 ) @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( r1_orders_2 @ X7 @ X6 @ X8 )
      | ~ ( r3_orders_2 @ X7 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X37: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('43',plain,(
    ! [X33: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('44',plain,(
    ! [X31: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ~ ( r1_orders_2 @ X17 @ X16 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X1 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X18 @ X19 @ X20 @ X21 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_2 @ X1 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D_1 @ X1 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( zip_tseitin_2 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) ) @ X2 @ X1 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( zip_tseitin_2 @ X0 @ k1_xboole_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X24
        = ( k1_yellow_0 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_2 @ X23 @ X24 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( k1_xboole_0
        = ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','63'])).

thf('65',plain,(
    ! [X31: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ( k1_xboole_0
      = ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('70',plain,(
    ! [X36: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X36 ) )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('71',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7WS45fVx9y
% 0.14/0.37  % Computer   : n003.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:04:27 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.37  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 160 iterations in 0.131s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.38/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.38/0.62  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.38/0.62  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.38/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.62  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.38/0.62  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.38/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.62  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.38/0.62  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.38/0.62  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.38/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.62  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.38/0.62  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.38/0.62  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.38/0.62  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.38/0.62  thf(t13_yellow_1, conjecture,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.62       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.38/0.62         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i]:
% 0.38/0.62        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.62          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.38/0.62            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.38/0.62  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d11_yellow_0, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_orders_2 @ A ) =>
% 0.38/0.62       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X13 : $i]:
% 0.38/0.62         (((k3_yellow_0 @ X13) = (k1_yellow_0 @ X13 @ k1_xboole_0))
% 0.38/0.62          | ~ (l1_orders_2 @ X13))),
% 0.38/0.62      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.38/0.62  thf('2', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t1_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.38/0.62  thf('4', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(t1_yellow_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.38/0.62       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.62  thf('5', plain, (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.62  thf(d9_lattice3, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_orders_2 @ A ) =>
% 0.38/0.62       ( ![B:$i,C:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.38/0.62             ( ![D:$i]:
% 0.38/0.62               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.38/0.62          | (r2_hidden @ (sk_D @ X9 @ X11 @ X10) @ X11)
% 0.38/0.62          | (r2_lattice3 @ X10 @ X11 @ X9)
% 0.38/0.62          | ~ (l1_orders_2 @ X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.38/0.62          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.38/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.62  thf(dt_k2_yellow_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.62       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.38/0.62  thf('8', plain, (![X31 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.38/0.62          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.38/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.38/0.62          | (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '9'])).
% 0.38/0.62  thf(d1_xboole_0, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.38/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.38/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.62  thf(t30_yellow_0, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 0.38/0.62                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 0.38/0.62                 ( ( ![D:$i]:
% 0.38/0.62                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.38/0.62                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.38/0.62                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 0.38/0.62               ( ( ( ![D:$i]:
% 0.38/0.62                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.38/0.62                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 0.38/0.62                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 0.38/0.62                 ( ( r1_yellow_0 @ A @ C ) & 
% 0.38/0.62                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_1, axiom,
% 0.38/0.62    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 0.38/0.62       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.62         ((zip_tseitin_1 @ X18 @ X19 @ X20 @ X21)
% 0.38/0.62          | (m1_subset_1 @ X18 @ (u1_struct_0 @ X21)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ (k2_yellow_1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.62  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_3, axiom,
% 0.38/0.62    (![C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.38/0.62       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 0.38/0.62  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_6, axiom,
% 0.38/0.62    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 0.38/0.62       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.38/0.62  thf(zf_stmt_7, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.38/0.62                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.38/0.62                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.38/0.62               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.38/0.62                   ( r1_yellow_0 @ A @ C ) ) =>
% 0.38/0.62                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 0.38/0.62                   ( ![D:$i]:
% 0.38/0.62                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.62                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.38/0.62                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i, X29 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.38/0.62          | ~ (r2_lattice3 @ X26 @ X29 @ X25)
% 0.38/0.62          | ~ (zip_tseitin_1 @ (sk_D_1 @ X29 @ X25 @ X26) @ X29 @ X25 @ X26)
% 0.38/0.62          | (zip_tseitin_2 @ X29 @ X25 @ X26)
% 0.38/0.62          | ~ (l1_orders_2 @ X26)
% 0.38/0.62          | ~ (v5_orders_2 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (zip_tseitin_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.38/0.62               X1 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.62  thf(fc5_yellow_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.62       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.62       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.38/0.62       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.38/0.62  thf('20', plain, (![X35 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X35))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.38/0.62  thf('21', plain, (![X31 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (zip_tseitin_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.38/0.62               X1 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.38/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((m1_subset_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X0)
% 0.38/0.62          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.38/0.62          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['16', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (m1_subset_1 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['13', '23'])).
% 0.38/0.62  thf('25', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (m1_subset_1 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (m1_subset_1 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf('28', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(t3_yellow_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.38/0.62               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.38/0.62                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X39 @ (u1_struct_0 @ (k2_yellow_1 @ X40)))
% 0.38/0.62          | ~ (r1_tarski @ X39 @ X41)
% 0.38/0.62          | (r3_orders_2 @ (k2_yellow_1 @ X40) @ X39 @ X41)
% 0.38/0.62          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ (k2_yellow_1 @ X40)))
% 0.38/0.62          | (v1_xboole_0 @ X40))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X39 @ X40)
% 0.38/0.62          | ~ (r1_tarski @ X39 @ X41)
% 0.38/0.62          | (r3_orders_2 @ (k2_yellow_1 @ X40) @ X39 @ X41)
% 0.38/0.62          | ~ (m1_subset_1 @ X41 @ X40)
% 0.38/0.62          | (v1_xboole_0 @ X40))),
% 0.38/0.62      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v1_xboole_0 @ sk_A)
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.38/0.62          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.38/0.62          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['28', '32'])).
% 0.38/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.62  thf('34', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v1_xboole_0 @ sk_A)
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.38/0.62          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.62  thf('36', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['35', '36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['27', '37'])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.62  thf(redefinition_r3_orders_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.38/0.62         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.62         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.38/0.62          | ~ (l1_orders_2 @ X7)
% 0.38/0.62          | ~ (v3_orders_2 @ X7)
% 0.38/0.62          | (v2_struct_0 @ X7)
% 0.38/0.62          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.38/0.62          | (r1_orders_2 @ X7 @ X6 @ X8)
% 0.38/0.62          | ~ (r3_orders_2 @ X7 @ X6 @ X8))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.62          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.62          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X37 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X37)) = (X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.38/0.62  thf('43', plain, (![X33 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X33))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.38/0.62  thf('44', plain, (![X31 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.62          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.38/0.62          | ~ (m1_subset_1 @ X2 @ X0)
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (m1_subset_1 @ 
% 0.38/0.62               (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.38/0.62          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.62          | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['38', '45'])).
% 0.38/0.62  thf('47', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (m1_subset_1 @ 
% 0.38/0.62               (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.38/0.62          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))))),
% 0.38/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['26', '48'])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.62         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.38/0.62          | ~ (r1_orders_2 @ X17 @ X16 @ X14))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (zip_tseitin_0 @ 
% 0.38/0.62             (sk_D_1 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X1 @ 
% 0.38/0.62             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.62         ((zip_tseitin_1 @ X18 @ X19 @ X20 @ X21)
% 0.38/0.62          | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X1)
% 0.38/0.62          | (zip_tseitin_2 @ X1 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (zip_tseitin_1 @ 
% 0.38/0.62             (sk_D_1 @ X1 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)) @ X0 @ 
% 0.38/0.62             k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X2 @ X1 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (zip_tseitin_1 @ (sk_D_1 @ X2 @ X1 @ (k2_yellow_1 @ X0)) @ X2 @ 
% 0.38/0.62               X1 @ (k2_yellow_1 @ X0))
% 0.38/0.62          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1))),
% 0.38/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.62  thf('57', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.62  thf('59', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['58'])).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['12', '59'])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | (zip_tseitin_2 @ X0 @ k1_xboole_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         (((X24) = (k1_yellow_0 @ X22 @ X23))
% 0.38/0.62          | ~ (zip_tseitin_2 @ X23 @ X24 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62          | ((k1_xboole_0) = (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.62        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.38/0.62        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['1', '63'])).
% 0.38/0.62  thf('65', plain, (![X31 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.38/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.62  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      ((((k1_xboole_0) = (k3_yellow_0 @ (k2_yellow_1 @ sk_A)))
% 0.38/0.62        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.38/0.62  thf('68', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('69', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.38/0.62  thf(fc6_yellow_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.62       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.38/0.62         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.38/0.62  thf('70', plain,
% 0.38/0.62      (![X36 : $i]:
% 0.38/0.62         (~ (v2_struct_0 @ (k2_yellow_1 @ X36)) | (v1_xboole_0 @ X36))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.38/0.62  thf('71', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.62  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
