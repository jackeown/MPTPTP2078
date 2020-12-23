%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MclkhBrxyo

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 442 expanded)
%              Number of leaves         :   21 ( 133 expanded)
%              Depth                    :   19
%              Number of atoms          : 1385 (7243 expanded)
%              Number of equality atoms :   49 ( 255 expanded)
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

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

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

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

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

thf('0',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r3_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ~ ( v2_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('15',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l28_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k11_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X9 @ X7 )
      | ~ ( r1_orders_2 @ X8 @ X9 @ X10 )
      | ( r1_orders_2 @ X8 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) @ X7 )
      | ( X9
        = ( k11_lattice3 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k12_lattice3 @ X13 @ X12 @ X14 )
        = ( k11_lattice3 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r3_orders_2 @ X3 @ X4 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('55',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['39','55'])).

thf('57',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['18','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('59',plain,
    ( ( ( sk_B
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X9 @ X7 )
      | ~ ( r1_orders_2 @ X8 @ X9 @ X10 )
      | ~ ( r1_orders_2 @ X8 @ ( sk_E @ X9 @ X10 @ X7 @ X8 ) @ X9 )
      | ( X9
        = ( k11_lattice3 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,
    ( ( ( sk_B
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( sk_B
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['53','54'])).

thf('70',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['12','17'])).

thf('71',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( sk_B
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_B
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('76',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      & ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('82',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('83',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( X9
       != ( k11_lattice3 @ X8 @ X7 @ X10 ) )
      | ( r1_orders_2 @ X8 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('84',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ ( k11_lattice3 @ X8 @ X7 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X8 @ X7 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('94',plain,
    ( ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('109',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,
    ( ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','79','80','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MclkhBrxyo
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 130 iterations in 0.100s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.55  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.55  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.21/0.55  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.21/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.55  thf(t25_yellow_0, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.21/0.55         ( l1_orders_2 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55               ( ( ( B ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.21/0.55                 ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.21/0.55            ( l1_orders_2 @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55                  ( ( ( B ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.21/0.55                    ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t25_yellow_0])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((~ (r3_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.21/0.55        | ((sk_B) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.21/0.55       ~ ((r3_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (((r3_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.21/0.55        | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (((r3_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.55         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['2'])).
% 0.21/0.55  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.55         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.55          | ~ (l1_orders_2 @ X1)
% 0.21/0.55          | ~ (v3_orders_2 @ X1)
% 0.21/0.55          | (v2_struct_0 @ X1)
% 0.21/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.55          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.55          | ~ (r3_orders_2 @ X1 @ X0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.55          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A)
% 0.21/0.55         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | (r1_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.55         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.55  thf('11', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.55         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_lattice3, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_orders_2 @ A ) =>
% 0.21/0.55       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X6 : $i]:
% 0.21/0.55         (~ (v2_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.21/0.55  thf('15', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v2_lattice3 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('16', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.55         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['12', '17'])).
% 0.21/0.55  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('20', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(l28_lattice3, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.55         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55               ( ![D:$i]:
% 0.21/0.55                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.21/0.55                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.21/0.55                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.21/0.55                       ( ![E:$i]:
% 0.21/0.55                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.21/0.55                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.21/0.55                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.55          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.55          | ~ (r1_orders_2 @ X8 @ X9 @ X7)
% 0.21/0.55          | ~ (r1_orders_2 @ X8 @ X9 @ X10)
% 0.21/0.55          | (r1_orders_2 @ X8 @ (sk_E @ X9 @ X10 @ X7 @ X8) @ X7)
% 0.21/0.55          | ((X9) = (k11_lattice3 @ X8 @ X7 @ X10))
% 0.21/0.55          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.55          | ~ (l1_orders_2 @ X8)
% 0.21/0.55          | ~ (v2_lattice3 @ X8)
% 0.21/0.55          | ~ (v5_orders_2 @ X8)
% 0.21/0.55          | (v2_struct_0 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.55          | ~ (v2_lattice3 @ sk_A)
% 0.21/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.21/0.55          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('25', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.21/0.55          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.21/0.55          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.55          | ((X0) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '27'])).
% 0.21/0.55  thf('29', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k12_lattice3, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.55          | ~ (l1_orders_2 @ X13)
% 0.21/0.55          | ~ (v2_lattice3 @ X13)
% 0.21/0.55          | ~ (v5_orders_2 @ X13)
% 0.21/0.55          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.55          | ((k12_lattice3 @ X13 @ X12 @ X14)
% 0.21/0.55              = (k11_lattice3 @ X13 @ X12 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k12_lattice3 @ sk_A @ sk_B @ X0)
% 0.21/0.55            = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.55          | ~ (v2_lattice3 @ sk_A)
% 0.21/0.55          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('34', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k12_lattice3 @ sk_A @ sk_B @ X0)
% 0.21/0.55            = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.21/0.55         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.21/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.21/0.55          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.55          | ((X0) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.55        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.55        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.21/0.55        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '38'])).
% 0.21/0.55  thf('40', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('41', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(reflexivity_r3_orders_2, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.55         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( r3_orders_2 @ A @ B @ B ) ))).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         ((r3_orders_2 @ X3 @ X4 @ X4)
% 0.21/0.55          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.21/0.55          | ~ (l1_orders_2 @ X3)
% 0.21/0.55          | ~ (v3_orders_2 @ X3)
% 0.21/0.55          | (v2_struct_0 @ X3)
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3)))),
% 0.21/0.55      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.55          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('44', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (r3_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.55  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r3_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf('49', plain, ((r3_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.21/0.55      inference('sup-', [status(thm)], ['40', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.55          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('55', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.21/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.55        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.55        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['39', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      ((((r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.55         | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.55         | (v2_struct_0 @ sk_A))) <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '56'])).
% 0.21/0.55  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B)))
% 0.21/0.56         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf('60', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.56          | ~ (r1_orders_2 @ X8 @ X9 @ X7)
% 0.21/0.56          | ~ (r1_orders_2 @ X8 @ X9 @ X10)
% 0.21/0.56          | ~ (r1_orders_2 @ X8 @ (sk_E @ X9 @ X10 @ X7 @ X8) @ X9)
% 0.21/0.56          | ((X9) = (k11_lattice3 @ X8 @ X7 @ X10))
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.56          | ~ (l1_orders_2 @ X8)
% 0.21/0.56          | ~ (v2_lattice3 @ X8)
% 0.21/0.56          | ~ (v5_orders_2 @ X8)
% 0.21/0.56          | (v2_struct_0 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v2_lattice3 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.21/0.56          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.21/0.56          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.56          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.56  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.21/0.56          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.21/0.56          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.56          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.21/0.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56         | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.21/0.56         | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.21/0.56         | ((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.56         | (v2_struct_0 @ sk_A))) <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['59', '66'])).
% 0.21/0.56  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('69', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.21/0.56      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('clc', [status(thm)], ['12', '17'])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.21/0.56         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.56  thf('72', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         | (v2_struct_0 @ sk_A))) <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '72'])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A) | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))
% 0.21/0.56         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.56  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.56         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      ((((sk_B) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.56         <= (~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      ((((sk_B) != (sk_B)))
% 0.21/0.56         <= (~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) & 
% 0.21/0.56             ((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.21/0.56       ~ ((r3_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.21/0.56       ((r3_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.56         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.21/0.56         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.56          | ((X9) != (k11_lattice3 @ X8 @ X7 @ X10))
% 0.21/0.56          | (r1_orders_2 @ X8 @ X9 @ X10)
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.56          | ~ (l1_orders_2 @ X8)
% 0.21/0.56          | ~ (v2_lattice3 @ X8)
% 0.21/0.56          | ~ (v5_orders_2 @ X8)
% 0.21/0.56          | (v2_struct_0 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X8)
% 0.21/0.56          | ~ (v5_orders_2 @ X8)
% 0.21/0.56          | ~ (v2_lattice3 @ X8)
% 0.21/0.56          | ~ (l1_orders_2 @ X8)
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.56          | (r1_orders_2 @ X8 @ (k11_lattice3 @ X8 @ X7 @ X10) @ X10)
% 0.21/0.56          | ~ (m1_subset_1 @ (k11_lattice3 @ X8 @ X7 @ X10) @ 
% 0.21/0.56               (u1_struct_0 @ X8))
% 0.21/0.56          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['83'])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.56           (u1_struct_0 @ sk_A))
% 0.21/0.56        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 0.21/0.56        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56        | ~ (v2_lattice3 @ sk_A)
% 0.21/0.56        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['82', '84'])).
% 0.21/0.56  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('87', plain,
% 0.21/0.56      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.21/0.56         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.56  thf('88', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('90', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('91', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('92', plain,
% 0.21/0.56      ((~ (m1_subset_1 @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.56           (u1_struct_0 @ sk_A))
% 0.21/0.56        | (r1_orders_2 @ sk_A @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['85', '86', '87', '88', '89', '90', '91'])).
% 0.21/0.56  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('94', plain,
% 0.21/0.56      (((r1_orders_2 @ sk_A @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 0.21/0.56        | ~ (m1_subset_1 @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.56             (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('clc', [status(thm)], ['92', '93'])).
% 0.21/0.56  thf('95', plain,
% 0.21/0.56      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.56         | (r1_orders_2 @ sk_A @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)))
% 0.21/0.56         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['81', '94'])).
% 0.21/0.56  thf('96', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.56         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('98', plain,
% 0.21/0.56      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.21/0.56  thf('99', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('100', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.56          | ~ (l1_orders_2 @ X1)
% 0.21/0.56          | ~ (v3_orders_2 @ X1)
% 0.21/0.56          | (v2_struct_0 @ X1)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.56          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.56          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.56  thf('101', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.56          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.56  thf('102', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('103', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('104', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.56          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A)
% 0.21/0.56         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.56         | (r3_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.56         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['98', '104'])).
% 0.21/0.56  thf('106', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('107', plain,
% 0.21/0.56      ((((v2_struct_0 @ sk_A) | (r3_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.56         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.56  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('109', plain,
% 0.21/0.56      (((r3_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.56      inference('clc', [status(thm)], ['107', '108'])).
% 0.21/0.56  thf('110', plain,
% 0.21/0.56      ((~ (r3_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.21/0.56         <= (~ ((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('111', plain,
% 0.21/0.56      (~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.21/0.56       ((r3_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.56  thf('112', plain, ($false),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['1', '79', '80', '111'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
