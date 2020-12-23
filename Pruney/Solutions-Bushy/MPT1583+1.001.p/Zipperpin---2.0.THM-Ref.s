%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1583+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NZbUc6BSXo

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:50 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 503 expanded)
%              Number of leaves         :   28 ( 147 expanded)
%              Depth                    :   27
%              Number of atoms          : 2251 (10303 expanded)
%              Number of equality atoms :    9 ( 204 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t62_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ! [E: $i] :
                  ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                 => ( ( E = D )
                   => ( ( ( r1_lattice3 @ A @ C @ D )
                       => ( r1_lattice3 @ B @ C @ E ) )
                      & ( ( r2_lattice3 @ A @ C @ D )
                       => ( r2_lattice3 @ B @ C @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_yellow_0 @ B @ A )
              & ( m1_yellow_0 @ B @ A ) )
           => ! [C: $i,D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ! [E: $i] :
                    ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                   => ( ( E = D )
                     => ( ( ( r1_lattice3 @ A @ C @ D )
                         => ( r1_lattice3 @ B @ C @ E ) )
                        & ( ( r2_lattice3 @ A @ C @ D )
                         => ( r2_lattice3 @ B @ C @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_yellow_0])).

thf('0',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_E = sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X6 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_yellow_0 @ X9 @ X10 )
      | ( l1_orders_2 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('15',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t59_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_yellow_0 @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_yellow_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_yellow_0 @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_orders_2 @ X5 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t61_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v4_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ( ( ( E = C )
                              & ( F = D )
                              & ( r1_orders_2 @ A @ C @ D )
                              & ( r2_hidden @ E @ ( u1_struct_0 @ B ) ) )
                           => ( r1_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v4_yellow_0 @ X19 @ X20 )
      | ~ ( m1_yellow_0 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X23 @ X22 )
      | ( X22 != X21 )
      | ~ ( r2_hidden @ X23 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X20 @ X24 @ X21 )
      | ( X23 != X24 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_yellow_0])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X20 @ X24 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( u1_struct_0 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_yellow_0 @ X19 @ X20 )
      | ~ ( v4_yellow_0 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_yellow_0 @ X1 @ sk_A )
      | ~ ( m1_yellow_0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X2 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_yellow_0 @ X1 @ sk_A )
      | ~ ( m1_yellow_0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X2 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_yellow_0 @ sk_B @ sk_A )
      | ~ ( v4_yellow_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v4_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X4 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
   <= ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,(
    sk_E = sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('76',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('79',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('80',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('85',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('94',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('101',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_yellow_0 @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_yellow_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_yellow_0 @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['93','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('116',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X19: $i,X20: $i,X21: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_orders_2 @ X20 @ X24 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( u1_struct_0 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_yellow_0 @ X19 @ X20 )
      | ~ ( v4_yellow_0 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D_2 @ X1 )
      | ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X1 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ sk_D_2 @ X1 )
      | ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X1 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) )
      | ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_yellow_0 @ X1 @ sk_A )
      | ~ ( v4_yellow_0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
        | ~ ( v4_yellow_0 @ X0 @ sk_A )
        | ~ ( m1_yellow_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ( r1_orders_2 @ X0 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
        | ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['114','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
        | ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
        | ( r1_orders_2 @ X0 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
        | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_yellow_0 @ X0 @ sk_A )
        | ~ ( v4_yellow_0 @ X0 @ sk_A )
        | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ~ ( v4_yellow_0 @ sk_B @ sk_A )
      | ~ ( m1_yellow_0 @ sk_B @ sk_A )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
      | ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['92','123'])).

thf('125',plain,(
    v4_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('128',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
      | ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( ~ ( r2_hidden @ sk_D_2 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['87','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
   <= ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['2'])).

thf('139',plain,(
    sk_E = sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
      & ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','83','84','151'])).


%------------------------------------------------------------------------------
