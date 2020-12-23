%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1537+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aVzcD1RIQY

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:45 EST 2020

% Result     : Theorem 4.90s
% Output     : Refutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 411 expanded)
%              Number of leaves         :   33 ( 125 expanded)
%              Depth                    :   28
%              Number of atoms          : 2577 (7363 expanded)
%              Number of equality atoms :   15 (  17 expanded)
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

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

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

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

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

thf(t15_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ C @ D ) ) )
              & ( r2_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( r1_yellow_0 @ A @ B )
          <=> ? [C: $i] :
                ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) )
                & ( r2_lattice3 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow_0])).

thf('0',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
      | ~ ( r1_orders_2 @ sk_A @ X34 @ ( sk_D_2 @ X34 ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ~ ( r1_orders_2 @ sk_A @ X34 @ ( sk_D_2 @ X34 ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 )
      | ( r1_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf(d7_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
              & ( r2_lattice3 @ A @ B @ C )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ C @ D ) ) )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( r2_lattice3 @ A @ B @ E )
                           => ( r1_orders_2 @ A @ D @ E ) ) )
                      & ( r2_lattice3 @ A @ B @ D ) )
                   => ( D = C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ B @ A )
       => ( D = C ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_3 @ X15 @ X18 @ X16 @ X19 )
      | ( zip_tseitin_2 @ X15 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('12',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ B @ A )
    <=> ( ( r2_lattice3 @ A @ B @ D )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
           => ( ( r2_lattice3 @ A @ B @ E )
             => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X12 @ X13 )
      | ~ ( r2_lattice3 @ X10 @ X11 @ X13 )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_2 @ X1 @ X0 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r1_orders_2 @ sk_A @ X1 @ sk_C_1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 )
        | ~ ( zip_tseitin_2 @ X0 @ sk_B @ sk_A ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_3 @ X0 @ X1 @ sk_B @ sk_A )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 ) )
   <= ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_lattice3 @ A @ B @ D )
       => ( r1_orders_2 @ A @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 )
      | ( r2_lattice3 @ X4 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X9 )
      | ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('22',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('23',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( ( zip_tseitin_1 @ X0 @ X3 @ sk_B @ sk_A )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
        | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_1 @ X1 @ X0 @ sk_B @ sk_A )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X1 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_1 @ X0 @ X2 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ X0 @ sk_C_1 @ X1 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_1 @ X1 @ X2 @ sk_B @ sk_A )
        | ( zip_tseitin_1 @ X1 @ sk_C_1 @ X0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_3 @ X15 @ X18 @ X16 @ X19 )
      | ( zip_tseitin_2 @ X15 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_lattice3 @ X10 @ X11 @ X12 )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_3 @ X2 @ X3 @ X1 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_4 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_3 @ D @ C @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_3 @ X20 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X1 @ X3 )
      | ( zip_tseitin_4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(zf_stmt_6,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( zip_tseitin_4 @ D @ C @ B @ A )
              & ! [D: $i] :
                  ( zip_tseitin_1 @ D @ C @ B @ A )
              & ( r2_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r2_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r1_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
        | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_C_1 )
        | ( r1_yellow_0 @ sk_A @ X0 )
        | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('45',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('47',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r2_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r1_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('56',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

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

thf('61',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_orders_2 @ X32 @ X31 @ X33 )
      | ~ ( r1_orders_2 @ X32 @ X33 @ X31 )
      | ( X31 = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_C_1 = X0 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( sk_C_1 = X0 )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C_1 )
        | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_3 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( sk_C_1
          = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','68'])).

thf('70',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_3 @ X20 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1
          = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
        | ( r1_yellow_0 @ sk_A @ sk_B )
        | ( zip_tseitin_4 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r2_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r1_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('73',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('76',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('78',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ( ( sk_C_1
        = ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X25 @ X26 @ X27 ) @ X25 @ X26 @ X27 )
      | ~ ( r2_lattice3 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X27 ) )
      | ( r1_yellow_0 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('81',plain,
    ( ( ~ ( zip_tseitin_4 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_3 @ X15 @ X18 @ X16 @ X19 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('83',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( zip_tseitin_3 @ X18 @ X18 @ X16 @ X19 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_4 @ X20 @ X22 @ X23 @ X24 )
      | ~ ( zip_tseitin_3 @ X20 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_4 @ X2 @ X2 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('88',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('90',plain,
    ( ( ( r1_yellow_0 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','85','86','87','88','89'])).

thf('91',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
      & ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( r1_yellow_0 @ sk_A @ sk_B )
   <= ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ~ ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ sk_C_1 @ X35 )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X35 ) )
    | ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
      | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('97',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_yellow_0 @ X27 @ X28 )
      | ( r2_lattice3 @ X27 @ X28 @ ( sk_C @ X28 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('98',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('102',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_yellow_0 @ X27 @ X28 )
      | ( m1_subset_1 @ ( sk_C @ X28 @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('103',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r1_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r1_yellow_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ( r1_yellow_0 @ sk_A @ sk_B )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('110',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_yellow_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ ( sk_C @ X28 @ X27 ) @ X28 @ X27 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('115',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['94'])).

thf('116',plain,
    ( ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X6 )
      | ~ ( zip_tseitin_1 @ X5 @ X7 @ X8 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('120',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( zip_tseitin_1 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ X1 @ X0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ X1 @ X0 @ sk_A ) )
   <= ( ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
   <= ( ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['113','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('123',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) ) )
   <= ( ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['108','123'])).

thf('125',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('126',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ~ ( r1_orders_2 @ sk_A @ X34 @ ( sk_D_2 @ X34 ) ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
        | ~ ( r1_orders_2 @ sk_A @ X34 @ ( sk_D_2 @ X34 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('127',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ~ ( r1_orders_2 @ sk_A @ X34 @ ( sk_D_2 @ X34 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) )
      & ( r1_yellow_0 @ sk_A @ sk_B )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ~ ( r1_orders_2 @ sk_A @ X34 @ ( sk_D_2 @ X34 ) ) )
      & ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
   <= ( r1_yellow_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('130',plain,
    ( ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ~ ( r1_orders_2 @ sk_A @ X34 @ ( sk_D_2 @ X34 ) ) )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_lattice3 @ sk_A @ sk_B @ X34 )
          | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D_2 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','93','95','130'])).


%------------------------------------------------------------------------------
