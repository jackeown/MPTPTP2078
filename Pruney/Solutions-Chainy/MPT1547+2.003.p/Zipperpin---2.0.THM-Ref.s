%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UYBw7vOXjb

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 756 expanded)
%              Number of leaves         :   21 ( 219 expanded)
%              Depth                    :   23
%              Number of atoms          : 1272 (12723 expanded)
%              Number of equality atoms :   44 ( 481 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

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

thf('0',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ~ ( v2_lattice3 @ X5 )
      | ~ ( v2_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('2',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_orders_2 @ X7 @ X8 @ X6 )
      | ~ ( r1_orders_2 @ X7 @ X8 @ X9 )
      | ( r1_orders_2 @ X7 @ ( sk_E @ X8 @ X9 @ X6 @ X7 ) @ X6 )
      | ( X8
        = ( k11_lattice3 @ X7 @ X6 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v2_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('9',plain,(
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
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( ( k12_lattice3 @ X12 @ X11 @ X13 )
        = ( k11_lattice3 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_B @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C )
      | ( r1_orders_2 @ sk_A @ ( sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X3 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('33',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['25','33'])).

thf('35',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r3_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('47',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['35'])).

thf('51',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( X8
       != ( k11_lattice3 @ X7 @ X6 @ X9 ) )
      | ( r1_orders_2 @ X7 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v2_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v2_lattice3 @ X7 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ( r1_orders_2 @ X7 @ ( k11_lattice3 @ X7 @ X6 @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X7 @ X6 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('63',plain,
    ( ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['35'])).

thf('67',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r3_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('78',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('80',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['35'])).

thf('82',plain,(
    r3_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['49','80','81'])).

thf('83',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['47','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','83'])).

thf('85',plain,
    ( ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['48'])).

thf('86',plain,(
    sk_B
 != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['49','80'])).

thf('87',plain,(
    sk_B
 != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['84','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('90',plain,(
    r1_orders_2 @ sk_A @ ( sk_E @ sk_B @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_orders_2 @ X7 @ X8 @ X6 )
      | ~ ( r1_orders_2 @ X7 @ X8 @ X9 )
      | ~ ( r1_orders_2 @ X7 @ ( sk_E @ X8 @ X9 @ X6 @ X7 ) @ X8 )
      | ( X8
        = ( k11_lattice3 @ X7 @ X6 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v2_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('93',plain,(
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
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( X1
        = ( k11_lattice3 @ sk_A @ sk_B @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E @ X1 @ X0 @ sk_B @ sk_A ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['31','32'])).

thf('101',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['47','82'])).

thf('102',plain,
    ( ( k12_lattice3 @ sk_A @ sk_B @ sk_C )
    = ( k11_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( sk_B
      = ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','103'])).

thf('105',plain,(
    sk_B
 != ( k12_lattice3 @ sk_A @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('106',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['4','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UYBw7vOXjb
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 72 iterations in 0.040s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(t25_yellow_0, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.20/0.50         ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ( ( B ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.50                 ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 0.20/0.50            ( l1_orders_2 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                  ( ( ( B ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.50                    ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t25_yellow_0])).
% 0.20/0.50  thf('0', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X5 : $i]:
% 0.20/0.50         (~ (v2_lattice3 @ X5) | ~ (v2_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.20/0.50  thf('2', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v2_lattice3 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l28_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.20/0.50         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.20/0.50                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.20/0.50                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.20/0.50                       ( ![E:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.20/0.50                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.20/0.50                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (r1_orders_2 @ X7 @ X8 @ X6)
% 0.20/0.50          | ~ (r1_orders_2 @ X7 @ X8 @ X9)
% 0.20/0.50          | (r1_orders_2 @ X7 @ (sk_E @ X8 @ X9 @ X6 @ X7) @ X6)
% 0.20/0.50          | ((X8) = (k11_lattice3 @ X7 @ X6 @ X9))
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l1_orders_2 @ X7)
% 0.20/0.50          | ~ (v2_lattice3 @ X7)
% 0.20/0.50          | ~ (v5_orders_2 @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.20/0.50          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50          | ((X0) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '13'])).
% 0.20/0.50  thf('15', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k12_lattice3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.20/0.50          | ~ (l1_orders_2 @ X12)
% 0.20/0.50          | ~ (v2_lattice3 @ X12)
% 0.20/0.50          | ~ (v5_orders_2 @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.50          | ((k12_lattice3 @ X12 @ X11 @ X13)
% 0.20/0.50              = (k11_lattice3 @ X12 @ X11 @ X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k12_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.50            = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k12_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.50            = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_C)
% 0.20/0.50          | (r1_orders_2 @ sk_A @ (sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50          | ((X0) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '24'])).
% 0.20/0.50  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t24_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.50          | (r1_orders_2 @ X4 @ X3 @ X3)
% 0.20/0.50          | ~ (l1_orders_2 @ X4)
% 0.20/0.50          | ~ (v3_orders_2 @ X4)
% 0.20/0.50          | (v2_struct_0 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('33', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.50        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((r3_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50        | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((r3_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['35'])).
% 0.20/0.50  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_r3_orders_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (l1_orders_2 @ X1)
% 0.20/0.50          | ~ (v3_orders_2 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.50          | ~ (r3_orders_2 @ X1 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.50         | (r1_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '42'])).
% 0.20/0.50  thf('44', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50         <= (((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((~ (r3_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50        | ((sk_B) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.50       ~ ((r3_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['35'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ((X8) != (k11_lattice3 @ X7 @ X6 @ X9))
% 0.20/0.50          | (r1_orders_2 @ X7 @ X8 @ X9)
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l1_orders_2 @ X7)
% 0.20/0.50          | ~ (v2_lattice3 @ X7)
% 0.20/0.50          | ~ (v5_orders_2 @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X7)
% 0.20/0.50          | ~ (v5_orders_2 @ X7)
% 0.20/0.50          | ~ (v2_lattice3 @ X7)
% 0.20/0.50          | ~ (l1_orders_2 @ X7)
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.50          | (r1_orders_2 @ X7 @ (k11_lattice3 @ X7 @ X6 @ X9) @ X9)
% 0.20/0.50          | ~ (m1_subset_1 @ (k11_lattice3 @ X7 @ X6 @ X9) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (k11_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 0.20/0.50        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.50        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '53'])).
% 0.20/0.50  thf('55', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('57', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.50           (u1_struct_0 @ sk_A))
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['54', '55', '56', '57', '58', '59', '60'])).
% 0.20/0.50  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (((r1_orders_2 @ sk_A @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 0.20/0.50        | ~ (m1_subset_1 @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.50             (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.50         | (r1_orders_2 @ sk_A @ (k12_lattice3 @ sk_A @ sk_B @ sk_C) @ sk_C)))
% 0.20/0.50         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '63'])).
% 0.20/0.50  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['35'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.50  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (l1_orders_2 @ X1)
% 0.20/0.50          | ~ (v3_orders_2 @ X1)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | (r3_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.50          | ~ (r1_orders_2 @ X1 @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | (r3_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A)
% 0.20/0.50         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.50         | (r3_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['67', '73'])).
% 0.20/0.50  thf('75', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (r3_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.50  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (((r3_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50         <= ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      ((~ (r3_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50         <= (~ ((r3_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      (((r3_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.50       ~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (((r3_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.20/0.50       (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['35'])).
% 0.20/0.50  thf('82', plain, (((r3_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['49', '80', '81'])).
% 0.20/0.50  thf('83', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['47', '82'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      ((((sk_B) != (k12_lattice3 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.50         <= (~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('86', plain, (~ (((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['49', '80'])).
% 0.20/0.50  thf('87', plain, (((sk_B) != (k12_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['84', '87'])).
% 0.20/0.50  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      ((r1_orders_2 @ sk_A @ (sk_E @ sk_B @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.50  thf('91', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (r1_orders_2 @ X7 @ X8 @ X6)
% 0.20/0.50          | ~ (r1_orders_2 @ X7 @ X8 @ X9)
% 0.20/0.50          | ~ (r1_orders_2 @ X7 @ (sk_E @ X8 @ X9 @ X6 @ X7) @ X8)
% 0.20/0.50          | ((X8) = (k11_lattice3 @ X7 @ X6 @ X9))
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l1_orders_2 @ X7)
% 0.20/0.50          | ~ (v2_lattice3 @ X7)
% 0.20/0.50          | ~ (v5_orders_2 @ X7)
% 0.20/0.50          | (v2_struct_0 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v2_lattice3 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.50  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('95', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('96', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((X1) = (k11_lattice3 @ sk_A @ sk_B @ X0))
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ (sk_E @ X1 @ X0 @ sk_B @ sk_A) @ X1)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ X1 @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.50        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50        | ((sk_B) = (k11_lattice3 @ sk_A @ sk_B @ sk_C))
% 0.20/0.50        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['90', '97'])).
% 0.20/0.50  thf('99', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('100', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('101', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['47', '82'])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      (((k12_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.50         = (k11_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('103', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      ((((sk_B) = (k12_lattice3 @ sk_A @ sk_B @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['98', '99', '100', '101', '102', '103'])).
% 0.20/0.50  thf('105', plain, (((sk_B) != (k12_lattice3 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.20/0.50  thf('106', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 0.20/0.50  thf('107', plain, ($false), inference('demod', [status(thm)], ['4', '106'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
