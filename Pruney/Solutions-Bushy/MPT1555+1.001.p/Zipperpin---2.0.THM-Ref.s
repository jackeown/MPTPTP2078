%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1555+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cgZbWJj92r

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 210 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          : 1229 (4016 expanded)
%              Number of equality atoms :   41 ( 128 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(t33_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( B
                = ( k2_yellow_0 @ A @ C ) )
            <=> ( ( r1_lattice3 @ A @ C @ B )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ C @ D )
                     => ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v5_orders_2 @ A )
          & ( v3_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( B
                  = ( k2_yellow_0 @ A @ C ) )
              <=> ( ( r1_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_yellow_0])).

thf('0',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

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
      ( ( ( r1_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ D @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X6 )
      | ( r1_lattice3 @ X6 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X7 @ X8 @ X9 @ X10 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X7 @ X8 @ X9 @ X10 )
      | ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 )
      | ( sk_B
        = ( k2_yellow_0 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X19: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) )
   <= ! [X19: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_B ) )
   <= ! [X19: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( ( zip_tseitin_1 @ X0 @ sk_C @ X3 @ sk_A )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
        | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A ) )
   <= ! [X19: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_1 @ X1 @ sk_C @ X0 @ sk_A )
        | ( r1_orders_2 @ sk_A @ X1 @ sk_B ) )
   <= ! [X19: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ),
    inference(condensation,[status(thm)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k2_yellow_0 @ A @ C ) )
        & ( r2_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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

thf('12',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_lattice3 @ X15 @ X18 @ X14 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X18 @ X14 @ X15 ) @ X18 @ X14 @ X15 )
      | ( zip_tseitin_2 @ X18 @ X14 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      | ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A ) )
   <= ! [X19: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X6 )
      | ~ ( r1_orders_2 @ X6 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X7 @ X8 @ X9 @ X10 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
        | ( zip_tseitin_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) )
   <= ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('24',plain,
    ( ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      | ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A ) )
   <= ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A ) )
   <= ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
   <= ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X13
        = ( k2_yellow_0 @ X11 @ X12 ) )
      | ~ ( zip_tseitin_2 @ X12 @ X13 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) )
   <= ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_1 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k2_yellow_0 @ sk_A @ sk_C ) )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
      & ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ~ ! [X19: $i] :
          ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
          | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
          | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_1 )
    | ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('40',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_1 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['30'])).

thf('41',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( X14
       != ( k2_yellow_0 @ X15 @ X16 ) )
      | ~ ( r2_yellow_0 @ X15 @ X16 )
      | ~ ( r1_lattice3 @ X15 @ X16 @ X17 )
      | ( r1_orders_2 @ X15 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ X17 @ ( k2_yellow_0 @ X15 @ X16 ) )
      | ~ ( r1_lattice3 @ X15 @ X16 @ X17 )
      | ~ ( r2_yellow_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_yellow_0 @ sk_A @ sk_C )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ ( k2_yellow_0 @ sk_A @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A ) )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
          & ( r1_yellow_0 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t17_yellow_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_lattice3 @ sk_A @ sk_C @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45','53','54','55','56'])).

thf('58',plain,
    ( ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_B ) )
   <= ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ sk_C ) )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['40','57'])).

thf('59',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_B )
   <= ( ( sk_B
        = ( k2_yellow_0 @ sk_A @ sk_C ) )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_D_1 )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','58'])).

thf('60',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('61',plain,
    ( ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_D_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X19: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X19 @ sk_B )
        | ~ ( r1_lattice3 @ sk_A @ sk_C @ X19 ) )
    | ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('63',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( X14
       != ( k2_yellow_0 @ X15 @ X16 ) )
      | ~ ( r2_yellow_0 @ X15 @ X16 )
      | ( r1_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ( r1_lattice3 @ X15 @ X16 @ ( k2_yellow_0 @ X15 @ X16 ) )
      | ~ ( r2_yellow_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X15 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_yellow_0 @ sk_A @ sk_C )
      | ( r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A ) )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( r2_yellow_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('70',plain,
    ( ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
   <= ( sk_B
      = ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('75',plain,
    ( ( sk_B
     != ( k2_yellow_0 @ sk_A @ sk_C ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['33','35','37','38','61','62','63','75'])).


%------------------------------------------------------------------------------
