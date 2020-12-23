%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1538+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l6r0sFeh6Y

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:45 EST 2020

% Result     : Theorem 4.70s
% Output     : Refutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 413 expanded)
%              Number of leaves         :   33 ( 125 expanded)
%              Depth                    :   22
%              Number of atoms          : 2585 (7371 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t16_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ D @ C ) ) )
              & ( r1_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( r2_yellow_0 @ A @ B )
          <=> ? [C: $i] :
                ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) )
                & ( r1_lattice3 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_yellow_0])).

thf('0',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 )
      | ( r2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) )
      | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ X34 ) @ X34 )
      | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ X34 ) @ X34 ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
      | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

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

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_yellow_0 @ X27 @ X28 )
      | ( r1_lattice3 @ X27 @ X28 @ ( sk_C @ X28 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('12',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_yellow_0 @ X27 @ X28 )
      | ( m1_subset_1 @ ( sk_C @ X28 @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('17',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_yellow_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ ( sk_C @ X28 @ X27 ) @ X28 @ X27 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('29',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('30',plain,
    ( ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X6 )
      | ~ ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('34',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ X1 @ X0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ X1 @ X0 @ sk_A ) )
   <= ( ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
   <= ( ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ X3 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('37',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) ) )
   <= ( ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('40',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ X34 ) @ X34 ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ X34 ) @ X34 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('41',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ X34 ) @ X34 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r2_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ X34 ) @ X34 ) )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,
    ( ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ X34 ) @ X34 ) )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 )
      | ( r1_lattice3 @ X4 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('49',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X9 )
      | ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('52',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( ( zip_tseitin_1 @ X0 @ X3 @ sk_B @ sk_A )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 )
        | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_1 @ X1 @ X0 @ sk_B @ sk_A )
        | ( r1_orders_2 @ sk_A @ X1 @ sk_C_1 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 )
      | ~ ( r1_orders_2 @ X4 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('57',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ sk_C_1 @ X1 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('59',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_1 @ X1 @ X2 @ sk_B @ sk_A )
        | ( zip_tseitin_1 @ X1 @ sk_C_1 @ X0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_3 @ X15 @ X18 @ X16 @ X19 )
      | ( zip_tseitin_2 @ X15 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('63',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_3 @ X20 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_2 @ X3 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r1_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r2_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r2_yellow_0 @ sk_A @ X0 )
        | ~ ( l1_orders_2 @ sk_A )
        | ( zip_tseitin_2 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ X0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r2_yellow_0 @ sk_A @ X0 )
        | ( zip_tseitin_2 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ X0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( zip_tseitin_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','70'])).

thf('72',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X13 @ X12 )
      | ~ ( r1_lattice3 @ X10 @ X11 @ X13 )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_2 @ X1 @ X0 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
        | ~ ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) )
   <= ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('79',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('81',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('82',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r1_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r2_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

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

thf('90',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_orders_2 @ X32 @ X31 @ X33 )
      | ~ ( r1_orders_2 @ X32 @ X33 @ X31 )
      | ( X31 = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_C_1 = X0 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_C_1 = X0 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','95'])).

thf('97',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_3 @ X15 @ X18 @ X16 @ X19 )
      | ( zip_tseitin_2 @ X15 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('102',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_lattice3 @ X10 @ X11 @ X12 )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_3 @ X2 @ X3 @ X1 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_3 @ X20 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r1_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r2_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattice3 @ X0 @ X1 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r2_yellow_0 @ sk_A @ X0 )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r2_yellow_0 @ sk_A @ X0 )
        | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','110'])).

thf('112',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('114',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['97','117'])).

thf('119',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r1_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r2_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('120',plain,
    ( ( ~ ( zip_tseitin_4 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_3 @ X15 @ X18 @ X16 @ X19 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('122',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( zip_tseitin_3 @ X18 @ X18 @ X16 @ X19 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_3 @ X20 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_4 @ X2 @ X2 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('127',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
        | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('129',plain,
    ( ( ( r2_yellow_0 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','124','125','126','127','128'])).

thf('130',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_B )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_B )
   <= ~ ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('132',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X35 @ sk_C_1 )
          | ~ ( r1_lattice3 @ sk_A @ sk_B @ X35 ) )
    | ( r2_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','44','46','132'])).


%------------------------------------------------------------------------------
