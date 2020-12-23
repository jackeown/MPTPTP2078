%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1547+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VJpeeQNs7s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:46 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 545 expanded)
%              Number of leaves         :   19 ( 158 expanded)
%              Depth                    :   16
%              Number of atoms          : 1072 (9107 expanded)
%              Number of equality atoms :   34 ( 333 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(t25_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( B
                  = ( k12_lattice3 @ A @ B @ C ) )
              <=> ( r3_orders_2 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( B
                    = ( k12_lattice3 @ A @ B @ C ) )
                <=> ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_yellow_0])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k12_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ X12 @ X10 )
      | ~ ( r1_orders_2 @ X11 @ X12 @ X13 )
      | ( r1_orders_2 @ X11 @ ( sk_E @ X12 @ X13 @ X10 @ X11 ) @ X10 )
      | ( X12
        = ( k12_lattice3 @ X11 @ X10 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k12_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k12_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r3_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('24',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['21','26'])).

thf('28',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X12
       != ( k12_lattice3 @ X11 @ X10 @ X13 ) )
      | ( r1_orders_2 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v5_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ ( k12_lattice3 @ X11 @ X10 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ ( k12_lattice3 @ X11 @ X10 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38','39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( r3_orders_2 @ X5 @ X4 @ X6 )
      | ~ ( r1_orders_2 @ X5 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('52',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('54',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('56',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['29','54','55'])).

thf('57',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['27','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('60',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r3_orders_2 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('73',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','57','73'])).

thf('75',plain,
    ( ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('76',plain,(
    sk_B
 != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['29','54'])).

thf('77',plain,(
    sk_B
 != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,(
    r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['74','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ X12 @ X10 )
      | ~ ( r1_orders_2 @ X11 @ X12 @ X13 )
      | ~ ( r1_orders_2 @ X11 @ ( sk_E @ X12 @ X13 @ X10 @ X11 ) @ X12 )
      | ( X12
        = ( k12_lattice3 @ X11 @ X10 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_yellow_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k12_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k12_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['71','72'])).

thf('89',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['27','56'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( sk_B
    = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,(
    sk_B
 != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('93',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).


%------------------------------------------------------------------------------
