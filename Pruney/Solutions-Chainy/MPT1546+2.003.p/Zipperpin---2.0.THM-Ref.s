%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.24szUzQQ2V

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:44 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 355 expanded)
%              Number of leaves         :   21 ( 109 expanded)
%              Depth                    :   19
%              Number of atoms          : 1227 (5875 expanded)
%              Number of equality atoms :   46 ( 216 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t24_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( B
                  = ( k13_lattice3 @ A @ B @ C ) )
              <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( B
                    = ( k13_lattice3 @ A @ B @ C ) )
                <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_0])).

thf('0',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l26_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k10_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ B @ D )
                      & ( r1_orders_2 @ A @ C @ D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ B @ E )
                              & ( r1_orders_2 @ A @ C @ E ) )
                           => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r1_orders_2 @ X8 @ X10 @ X9 )
      | ( r1_orders_2 @ X8 @ X7 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) )
      | ( X9
        = ( k10_lattice3 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k13_lattice3 @ X13 @ X12 @ X14 )
        = ( k10_lattice3 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k13_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r3_orders_2 @ X3 @ X4 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i] :
      ( ~ ( v1_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('34',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('38',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['25','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r3_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('49',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['24','49'])).

thf('51',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) )
      | ( sk_B
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('53',plain,
    ( ( ( sk_B
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r1_orders_2 @ X8 @ X10 @ X9 )
      | ~ ( r1_orders_2 @ X8 @ X9 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) )
      | ( X9
        = ( k10_lattice3 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k10_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ( ( sk_B
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
      | ( sk_B
        = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['47','48'])).

thf('64',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( sk_B
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_B
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('70',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('77',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( X9
       != ( k10_lattice3 @ X8 @ X7 @ X10 ) )
      | ( r1_orders_2 @ X8 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l26_lattice3])).

thf('78',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X10 @ ( k10_lattice3 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_subset_1 @ ( k10_lattice3 @ X8 @ X7 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( m1_subset_1 @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k13_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k10_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('88',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('92',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( sk_B
      = ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,
    ( ( sk_B
     != ( k13_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','73','74','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.24szUzQQ2V
% 0.14/0.38  % Computer   : n001.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 20:46:00 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.24/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.60  % Solved by: fo/fo7.sh
% 0.24/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.60  % done 129 iterations in 0.101s
% 0.24/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.60  % SZS output start Refutation
% 0.24/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.60  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.24/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.60  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.24/0.60  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.24/0.60  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.24/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.60  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.24/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.60  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.24/0.60  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.24/0.60  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.24/0.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.24/0.60  thf(t24_yellow_0, conjecture,
% 0.24/0.60    (![A:$i]:
% 0.24/0.60     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.24/0.60         ( l1_orders_2 @ A ) ) =>
% 0.24/0.60       ( ![B:$i]:
% 0.24/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60           ( ![C:$i]:
% 0.24/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60               ( ( ( B ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.24/0.60                 ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.60    (~( ![A:$i]:
% 0.24/0.60        ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.24/0.60            ( l1_orders_2 @ A ) ) =>
% 0.24/0.60          ( ![B:$i]:
% 0.24/0.60            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60              ( ![C:$i]:
% 0.24/0.60                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60                  ( ( ( B ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.24/0.60                    ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ) )),
% 0.24/0.60    inference('cnf.neg', [status(esa)], [t24_yellow_0])).
% 0.24/0.60  thf('0', plain,
% 0.24/0.60      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.24/0.60        | ((sk_B) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('1', plain,
% 0.24/0.60      (~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.24/0.60       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.24/0.60      inference('split', [status(esa)], ['0'])).
% 0.24/0.60  thf('2', plain,
% 0.24/0.60      (((r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.24/0.60        | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('3', plain,
% 0.24/0.60      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.24/0.60         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('split', [status(esa)], ['2'])).
% 0.24/0.60  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('5', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf(l26_lattice3, axiom,
% 0.24/0.60    (![A:$i]:
% 0.24/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.24/0.60         ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.24/0.60       ( ![B:$i]:
% 0.24/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60           ( ![C:$i]:
% 0.24/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60               ( ![D:$i]:
% 0.24/0.60                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60                   ( ( ( D ) = ( k10_lattice3 @ A @ B @ C ) ) <=>
% 0.24/0.60                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.24/0.60                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.24/0.60                       ( ![E:$i]:
% 0.24/0.60                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.60                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.24/0.60                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.24/0.60                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.60  thf('7', plain,
% 0.24/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (r1_orders_2 @ X8 @ X7 @ X9)
% 0.24/0.60          | ~ (r1_orders_2 @ X8 @ X10 @ X9)
% 0.24/0.60          | (r1_orders_2 @ X8 @ X7 @ (sk_E @ X9 @ X10 @ X7 @ X8))
% 0.24/0.60          | ((X9) = (k10_lattice3 @ X8 @ X7 @ X10))
% 0.24/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (l1_orders_2 @ X8)
% 0.24/0.60          | ~ (v1_lattice3 @ X8)
% 0.24/0.60          | ~ (v5_orders_2 @ X8)
% 0.24/0.60          | (v2_struct_0 @ X8))),
% 0.24/0.60      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.24/0.60  thf('8', plain,
% 0.24/0.60      (![X0 : $i, X1 : $i]:
% 0.24/0.60         ((v2_struct_0 @ sk_A)
% 0.24/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.24/0.60          | ~ (v1_lattice3 @ sk_A)
% 0.24/0.60          | ~ (l1_orders_2 @ sk_A)
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.24/0.60          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.24/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.60  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('10', plain, ((v1_lattice3 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('12', plain,
% 0.24/0.60      (![X0 : $i, X1 : $i]:
% 0.24/0.60         ((v2_struct_0 @ sk_A)
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.24/0.60          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.24/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.60      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.24/0.60  thf('13', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.24/0.60          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.24/0.60          | ((X0) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60          | (v2_struct_0 @ sk_A))),
% 0.24/0.60      inference('sup-', [status(thm)], ['5', '12'])).
% 0.24/0.60  thf('14', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf(redefinition_k13_lattice3, axiom,
% 0.24/0.60    (![A:$i,B:$i,C:$i]:
% 0.24/0.60     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.24/0.60         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.24/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.60       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.24/0.60  thf('16', plain,
% 0.24/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.24/0.60          | ~ (l1_orders_2 @ X13)
% 0.24/0.60          | ~ (v1_lattice3 @ X13)
% 0.24/0.60          | ~ (v5_orders_2 @ X13)
% 0.24/0.60          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.24/0.60          | ((k13_lattice3 @ X13 @ X12 @ X14)
% 0.24/0.60              = (k10_lattice3 @ X13 @ X12 @ X14)))),
% 0.24/0.60      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.24/0.60  thf('17', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (((k13_lattice3 @ sk_A @ sk_B @ X0)
% 0.24/0.60            = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.24/0.60          | ~ (v1_lattice3 @ sk_A)
% 0.24/0.60          | ~ (l1_orders_2 @ sk_A))),
% 0.24/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.60  thf('18', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('19', plain, ((v1_lattice3 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('21', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (((k13_lattice3 @ sk_A @ sk_B @ X0)
% 0.24/0.60            = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.60      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.24/0.60  thf('22', plain,
% 0.24/0.60      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.24/0.60         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.24/0.60      inference('sup-', [status(thm)], ['14', '21'])).
% 0.24/0.60  thf('23', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.24/0.60          | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.24/0.60          | ((X0) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60          | (v2_struct_0 @ sk_A))),
% 0.24/0.60      inference('demod', [status(thm)], ['13', '22'])).
% 0.24/0.60  thf('24', plain,
% 0.24/0.60      (((v2_struct_0 @ sk_A)
% 0.24/0.60        | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60        | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A))
% 0.24/0.60        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.24/0.60        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.24/0.60      inference('sup-', [status(thm)], ['4', '23'])).
% 0.24/0.60  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf(reflexivity_r3_orders_2, axiom,
% 0.24/0.60    (![A:$i,B:$i,C:$i]:
% 0.24/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.60         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.24/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.60       ( r3_orders_2 @ A @ B @ B ) ))).
% 0.24/0.60  thf('27', plain,
% 0.24/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.60         ((r3_orders_2 @ X3 @ X4 @ X4)
% 0.24/0.60          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.24/0.60          | ~ (l1_orders_2 @ X3)
% 0.24/0.60          | ~ (v3_orders_2 @ X3)
% 0.24/0.60          | (v2_struct_0 @ X3)
% 0.24/0.60          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3)))),
% 0.24/0.60      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.24/0.60  thf('28', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | (v2_struct_0 @ sk_A)
% 0.24/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.24/0.60          | ~ (l1_orders_2 @ sk_A)
% 0.24/0.60          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.24/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.60  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('31', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | (v2_struct_0 @ sk_A)
% 0.24/0.60          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.24/0.60      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.24/0.60  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf(cc1_lattice3, axiom,
% 0.24/0.60    (![A:$i]:
% 0.24/0.60     ( ( l1_orders_2 @ A ) =>
% 0.24/0.60       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.24/0.60  thf('33', plain,
% 0.24/0.60      (![X6 : $i]:
% 0.24/0.60         (~ (v1_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.24/0.60      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.24/0.60  thf('34', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.24/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.60  thf('35', plain, ((v1_lattice3 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.60  thf('37', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         ((r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.60      inference('clc', [status(thm)], ['31', '36'])).
% 0.24/0.60  thf('38', plain, ((r3_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.24/0.60      inference('sup-', [status(thm)], ['25', '37'])).
% 0.24/0.60  thf('39', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf(redefinition_r3_orders_2, axiom,
% 0.24/0.60    (![A:$i,B:$i,C:$i]:
% 0.24/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.24/0.60         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.24/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.60       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.24/0.60  thf('40', plain,
% 0.24/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.24/0.60          | ~ (l1_orders_2 @ X1)
% 0.24/0.60          | ~ (v3_orders_2 @ X1)
% 0.24/0.60          | (v2_struct_0 @ X1)
% 0.24/0.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.60          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.24/0.60          | ~ (r3_orders_2 @ X1 @ X0 @ X2))),
% 0.24/0.60      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.24/0.60  thf('41', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.24/0.60          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | (v2_struct_0 @ sk_A)
% 0.24/0.60          | ~ (v3_orders_2 @ sk_A)
% 0.24/0.60          | ~ (l1_orders_2 @ sk_A))),
% 0.24/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.24/0.60  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('44', plain,
% 0.24/0.60      (![X0 : $i]:
% 0.24/0.60         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.24/0.60          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | (v2_struct_0 @ sk_A))),
% 0.24/0.60      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.24/0.60  thf('45', plain,
% 0.24/0.60      (((v2_struct_0 @ sk_A)
% 0.24/0.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.60        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.24/0.60      inference('sup-', [status(thm)], ['38', '44'])).
% 0.24/0.60  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('47', plain,
% 0.24/0.60      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.24/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.24/0.60  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.60  thf('49', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.24/0.60      inference('clc', [status(thm)], ['47', '48'])).
% 0.24/0.60  thf('50', plain,
% 0.24/0.60      (((v2_struct_0 @ sk_A)
% 0.24/0.60        | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60        | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A))
% 0.24/0.60        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.24/0.60      inference('demod', [status(thm)], ['24', '49'])).
% 0.24/0.60  thf('51', plain,
% 0.24/0.60      ((((r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A))
% 0.24/0.60         | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60         | (v2_struct_0 @ sk_A))) <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('sup-', [status(thm)], ['3', '50'])).
% 0.24/0.60  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.60  thf('53', plain,
% 0.24/0.60      (((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60         | (r1_orders_2 @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A))))
% 0.24/0.60         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('clc', [status(thm)], ['51', '52'])).
% 0.24/0.60  thf('54', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('55', plain,
% 0.24/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (r1_orders_2 @ X8 @ X7 @ X9)
% 0.24/0.60          | ~ (r1_orders_2 @ X8 @ X10 @ X9)
% 0.24/0.60          | ~ (r1_orders_2 @ X8 @ X9 @ (sk_E @ X9 @ X10 @ X7 @ X8))
% 0.24/0.60          | ((X9) = (k10_lattice3 @ X8 @ X7 @ X10))
% 0.24/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (l1_orders_2 @ X8)
% 0.24/0.60          | ~ (v1_lattice3 @ X8)
% 0.24/0.60          | ~ (v5_orders_2 @ X8)
% 0.24/0.60          | (v2_struct_0 @ X8))),
% 0.24/0.60      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.24/0.60  thf('56', plain,
% 0.24/0.60      (![X0 : $i, X1 : $i]:
% 0.24/0.60         ((v2_struct_0 @ sk_A)
% 0.24/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.24/0.60          | ~ (v1_lattice3 @ sk_A)
% 0.24/0.60          | ~ (l1_orders_2 @ sk_A)
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.24/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.24/0.60  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('58', plain, ((v1_lattice3 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('60', plain,
% 0.24/0.60      (![X0 : $i, X1 : $i]:
% 0.24/0.60         ((v2_struct_0 @ sk_A)
% 0.24/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.24/0.60          | ((X1) = (k10_lattice3 @ sk_A @ sk_B @ X0))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ X1 @ (sk_E @ X1 @ X0 @ sk_B @ sk_A))
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.24/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X1)
% 0.24/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.60      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.24/0.60  thf('61', plain,
% 0.24/0.60      (((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.60         | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.24/0.60         | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.24/0.60         | ((sk_B) = (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.24/0.60         | (v2_struct_0 @ sk_A))) <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('sup-', [status(thm)], ['53', '60'])).
% 0.24/0.60  thf('62', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('63', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.24/0.60      inference('clc', [status(thm)], ['47', '48'])).
% 0.24/0.60  thf('64', plain,
% 0.24/0.60      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.24/0.60         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('split', [status(esa)], ['2'])).
% 0.24/0.60  thf('65', plain,
% 0.24/0.60      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.24/0.60         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.24/0.60      inference('sup-', [status(thm)], ['14', '21'])).
% 0.24/0.60  thf('66', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('67', plain,
% 0.24/0.60      (((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60         | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60         | (v2_struct_0 @ sk_A))) <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('demod', [status(thm)], ['61', '62', '63', '64', '65', '66'])).
% 0.24/0.60  thf('68', plain,
% 0.24/0.60      ((((v2_struct_0 @ sk_A) | ((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.24/0.60         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('simplify', [status(thm)], ['67'])).
% 0.24/0.60  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.60  thf('70', plain,
% 0.24/0.60      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.60         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('clc', [status(thm)], ['68', '69'])).
% 0.24/0.60  thf('71', plain,
% 0.24/0.60      ((((sk_B) != (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.60         <= (~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.60      inference('split', [status(esa)], ['0'])).
% 0.24/0.60  thf('72', plain,
% 0.24/0.60      ((((sk_B) != (sk_B)))
% 0.24/0.60         <= (~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.24/0.60             ((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.24/0.60  thf('73', plain,
% 0.24/0.60      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.24/0.60       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.24/0.60      inference('simplify', [status(thm)], ['72'])).
% 0.24/0.60  thf('74', plain,
% 0.24/0.60      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.24/0.60       ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.24/0.60      inference('split', [status(esa)], ['2'])).
% 0.24/0.60  thf('75', plain,
% 0.24/0.60      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.60         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.60      inference('split', [status(esa)], ['2'])).
% 0.24/0.60  thf('76', plain,
% 0.24/0.60      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.24/0.60         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.24/0.60      inference('sup-', [status(thm)], ['14', '21'])).
% 0.24/0.60  thf('77', plain,
% 0.24/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ((X9) != (k10_lattice3 @ X8 @ X7 @ X10))
% 0.24/0.60          | (r1_orders_2 @ X8 @ X10 @ X9)
% 0.24/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (l1_orders_2 @ X8)
% 0.24/0.60          | ~ (v1_lattice3 @ X8)
% 0.24/0.60          | ~ (v5_orders_2 @ X8)
% 0.24/0.60          | (v2_struct_0 @ X8))),
% 0.24/0.60      inference('cnf', [status(esa)], [l26_lattice3])).
% 0.24/0.60  thf('78', plain,
% 0.24/0.60      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.24/0.60         ((v2_struct_0 @ X8)
% 0.24/0.60          | ~ (v5_orders_2 @ X8)
% 0.24/0.60          | ~ (v1_lattice3 @ X8)
% 0.24/0.60          | ~ (l1_orders_2 @ X8)
% 0.24/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.24/0.60          | (r1_orders_2 @ X8 @ X10 @ (k10_lattice3 @ X8 @ X7 @ X10))
% 0.24/0.60          | ~ (m1_subset_1 @ (k10_lattice3 @ X8 @ X7 @ X10) @ 
% 0.24/0.60               (u1_struct_0 @ X8))
% 0.24/0.60          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8)))),
% 0.24/0.60      inference('simplify', [status(thm)], ['77'])).
% 0.24/0.60  thf('79', plain,
% 0.24/0.60      ((~ (m1_subset_1 @ (k13_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.60           (u1_struct_0 @ sk_A))
% 0.24/0.60        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.60        | (r1_orders_2 @ sk_A @ sk_C @ (k10_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.24/0.60        | ~ (l1_orders_2 @ sk_A)
% 0.24/0.60        | ~ (v1_lattice3 @ sk_A)
% 0.24/0.60        | ~ (v5_orders_2 @ sk_A)
% 0.24/0.60        | (v2_struct_0 @ sk_A))),
% 0.24/0.60      inference('sup-', [status(thm)], ['76', '78'])).
% 0.24/0.60  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('81', plain,
% 0.24/0.60      (((k13_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.24/0.60         = (k10_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.24/0.60      inference('sup-', [status(thm)], ['14', '21'])).
% 0.24/0.60  thf('82', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('84', plain, ((v1_lattice3 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('85', plain, ((v5_orders_2 @ sk_A)),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('86', plain,
% 0.24/0.60      ((~ (m1_subset_1 @ (k13_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.60           (u1_struct_0 @ sk_A))
% 0.24/0.60        | (r1_orders_2 @ sk_A @ sk_C @ (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60        | (v2_struct_0 @ sk_A))),
% 0.24/0.60      inference('demod', [status(thm)],
% 0.24/0.60                ['79', '80', '81', '82', '83', '84', '85'])).
% 0.24/0.60  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.60  thf('88', plain,
% 0.24/0.60      (((r1_orders_2 @ sk_A @ sk_C @ (k13_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.24/0.60        | ~ (m1_subset_1 @ (k13_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.60             (u1_struct_0 @ sk_A)))),
% 0.24/0.60      inference('clc', [status(thm)], ['86', '87'])).
% 0.24/0.60  thf('89', plain,
% 0.24/0.60      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.60         | (r1_orders_2 @ sk_A @ sk_C @ (k13_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.24/0.60         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.60      inference('sup-', [status(thm)], ['75', '88'])).
% 0.24/0.60  thf('90', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.60  thf('91', plain,
% 0.24/0.60      ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.60         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.60      inference('split', [status(esa)], ['2'])).
% 0.24/0.60  thf('92', plain,
% 0.24/0.60      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.24/0.60         <= ((((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.60      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.24/0.60  thf('93', plain,
% 0.24/0.60      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.24/0.60         <= (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.24/0.60      inference('split', [status(esa)], ['0'])).
% 0.24/0.60  thf('94', plain,
% 0.24/0.60      (~ (((sk_B) = (k13_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.24/0.60       ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.24/0.60      inference('sup-', [status(thm)], ['92', '93'])).
% 0.24/0.60  thf('95', plain, ($false),
% 0.24/0.60      inference('sat_resolution*', [status(thm)], ['1', '73', '74', '94'])).
% 0.24/0.60  
% 0.24/0.60  % SZS output end Refutation
% 0.24/0.60  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
