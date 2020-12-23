%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d2qRShKnXi

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 260 expanded)
%              Number of leaves         :   17 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  942 (5887 expanded)
%              Number of equality atoms :   10 (  34 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(t7_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ B @ C ) )
                & ( ( r1_orders_2 @ A @ B @ C )
                 => ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) )
                & ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                 => ( r1_orders_2 @ A @ C @ B ) )
                & ( ( r1_orders_2 @ A @ C @ B )
                 => ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                   => ( r1_orders_2 @ A @ B @ C ) )
                  & ( ( r1_orders_2 @ A @ B @ C )
                   => ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) )
                  & ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B )
                   => ( r1_orders_2 @ A @ C @ B ) )
                  & ( ( r1_orders_2 @ A @ C @ B )
                   => ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_yellow_0])).

thf('0',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_orders_2 @ X10 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
      | ~ ( r2_hidden @ sk_C_1 @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X11 @ X10 ) @ X11 )
      | ( r2_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( ( sk_D_1 @ sk_B @ ( k1_tarski @ X0 ) @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_orders_2 @ X10 @ ( sk_D_1 @ X9 @ X11 @ X10 ) @ X9 )
      | ( r2_lattice3 @ X10 @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
   <= ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_lattice3 @ X6 @ X7 @ X5 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_orders_2 @ X6 @ X5 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('47',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X7 )
      | ( r1_lattice3 @ X6 @ X7 @ X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( ( sk_D @ sk_B @ ( k1_tarski @ X0 ) @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_orders_2 @ X6 @ X5 @ ( sk_D @ X5 @ X7 @ X6 ) )
      | ( r1_lattice3 @ X6 @ X7 @ X5 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','64'])).

thf('66',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('69',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('70',plain,(
    ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['49','67','1','68','69'])).

thf('71',plain,(
    ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['36','70'])).

thf('72',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','71'])).

thf('73',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','16','18','72','49','73','75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d2qRShKnXi
% 0.14/0.36  % Computer   : n009.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:08:56 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 111 iterations in 0.067s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.23/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.54  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.23/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.23/0.54  thf(t7_yellow_0, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_orders_2 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.23/0.54                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.23/0.54                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.23/0.54                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.23/0.54                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.23/0.54                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.23/0.54                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.23/0.54                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( l1_orders_2 @ A ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54              ( ![C:$i]:
% 0.23/0.54                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54                  ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.23/0.54                      ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.23/0.54                    ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.23/0.54                      ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.23/0.54                    ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.23/0.54                      ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.23/0.54                    ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.23/0.54                      ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t7_yellow_0])).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.23/0.54        | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.23/0.54        | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 0.23/0.54        | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.23/0.54       ~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ~ ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.23/0.54        | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.23/0.54        | (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.23/0.54        | (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))
% 0.23/0.54         <= (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['2'])).
% 0.23/0.54  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d9_lattice3, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_orders_2 @ A ) =>
% 0.23/0.54       ( ![B:$i,C:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.23/0.54             ( ![D:$i]:
% 0.23/0.54               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.23/0.54          | ~ (r2_lattice3 @ X10 @ X11 @ X9)
% 0.23/0.54          | ~ (r2_hidden @ X12 @ X11)
% 0.23/0.54          | (r1_orders_2 @ X10 @ X12 @ X9)
% 0.23/0.54          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.23/0.54          | ~ (l1_orders_2 @ X10))),
% 0.23/0.54      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ X1)
% 0.23/0.54          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ X1)
% 0.23/0.54          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.23/0.54          | (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      ((((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 0.23/0.54         | ~ (r2_hidden @ sk_C_1 @ (k1_tarski @ sk_C_1))))
% 0.23/0.54         <= (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['3', '10'])).
% 0.23/0.54  thf(d1_tarski, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.54  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 0.23/0.54         <= (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('demod', [status(thm)], ['11', '13'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 0.23/0.54         <= (~ ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.23/0.54        | (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.23/0.54        | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 0.23/0.54        | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.23/0.54       ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ~ ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('split', [status(esa)], ['17'])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))
% 0.23/0.54         <= (((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['2'])).
% 0.23/0.54  thf('20', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.23/0.54          | (r2_hidden @ (sk_D_1 @ X9 @ X11 @ X10) @ X11)
% 0.23/0.54          | (r2_lattice3 @ X10 @ X11 @ X9)
% 0.23/0.54          | ~ (l1_orders_2 @ X10))),
% 0.23/0.54      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.54  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      (![X0 : $i, X3 : $i]:
% 0.23/0.54         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.23/0.54          | ((sk_D_1 @ sk_B @ (k1_tarski @ X0) @ sk_A) = (X0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['24', '26'])).
% 0.23/0.54  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.23/0.54          | ~ (r1_orders_2 @ X10 @ (sk_D_1 @ X9 @ X11 @ X10) @ X9)
% 0.23/0.54          | (r2_lattice3 @ X10 @ X11 @ X9)
% 0.23/0.54          | ~ (l1_orders_2 @ X10))),
% 0.23/0.54      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.54  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.23/0.54          | (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['27', '32'])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.23/0.54          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.23/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))
% 0.23/0.54         <= (((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '34'])).
% 0.23/0.54  thf('36', plain,
% 0.23/0.54      ((~ (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))
% 0.23/0.54         <= (~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('37', plain,
% 0.23/0.54      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))
% 0.23/0.54         <= (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['17'])).
% 0.23/0.54  thf('38', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('39', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d8_lattice3, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_orders_2 @ A ) =>
% 0.23/0.54       ( ![B:$i,C:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.23/0.54             ( ![D:$i]:
% 0.23/0.54               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.23/0.54          | ~ (r1_lattice3 @ X6 @ X7 @ X5)
% 0.23/0.54          | ~ (r2_hidden @ X8 @ X7)
% 0.23/0.54          | (r1_orders_2 @ X6 @ X5 @ X8)
% 0.23/0.54          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.23/0.54          | ~ (l1_orders_2 @ X6))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ X1)
% 0.23/0.54          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.23/0.54  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('43', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ X1)
% 0.23/0.54          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.23/0.54          | (r1_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['38', '43'])).
% 0.23/0.54  thf('45', plain,
% 0.23/0.54      ((((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.23/0.54         | ~ (r2_hidden @ sk_C_1 @ (k1_tarski @ sk_C_1))))
% 0.23/0.54         <= (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['37', '44'])).
% 0.23/0.54  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.54  thf('47', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.23/0.54         <= (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.23/0.54  thf('48', plain,
% 0.23/0.54      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.23/0.54         <= (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('49', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.23/0.54       ~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.23/0.54  thf('50', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.23/0.54         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.23/0.54      inference('split', [status(esa)], ['17'])).
% 0.23/0.54  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('52', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.23/0.54          | (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X7)
% 0.23/0.54          | (r1_lattice3 @ X6 @ X7 @ X5)
% 0.23/0.54          | ~ (l1_orders_2 @ X6))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.23/0.54  thf('53', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.23/0.54  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('55', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 0.23/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.23/0.54  thf('56', plain,
% 0.23/0.54      (![X0 : $i, X3 : $i]:
% 0.23/0.54         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.54  thf('57', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.23/0.54          | ((sk_D @ sk_B @ (k1_tarski @ X0) @ sk_A) = (X0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.54  thf('58', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('59', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.23/0.54          | ~ (r1_orders_2 @ X6 @ X5 @ (sk_D @ X5 @ X7 @ X6))
% 0.23/0.54          | (r1_lattice3 @ X6 @ X7 @ X5)
% 0.23/0.54          | ~ (l1_orders_2 @ X6))),
% 0.23/0.54      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.23/0.54  thf('60', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.23/0.54  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('62', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.23/0.54          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 0.23/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.23/0.54  thf('63', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.23/0.54          | (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.23/0.54          | (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['57', '62'])).
% 0.23/0.54  thf('64', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.23/0.54          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['63'])).
% 0.23/0.54  thf('65', plain,
% 0.23/0.54      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))
% 0.23/0.54         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['50', '64'])).
% 0.23/0.54  thf('66', plain,
% 0.23/0.54      ((~ (r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))
% 0.23/0.54         <= (~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['0'])).
% 0.23/0.54  thf('67', plain,
% 0.23/0.54      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.54  thf('68', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)) | 
% 0.23/0.54       ~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.54  thf('69', plain,
% 0.23/0.54      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.23/0.54       ~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ~ ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('split', [status(esa)], ['17'])).
% 0.23/0.54  thf('70', plain, (~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['49', '67', '1', '68', '69'])).
% 0.23/0.54  thf('71', plain, (~ (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['36', '70'])).
% 0.23/0.54  thf('72', plain, (~ ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['35', '71'])).
% 0.23/0.54  thf('73', plain,
% 0.23/0.54      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.23/0.54       ~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('split', [status(esa)], ['2'])).
% 0.23/0.54  thf('74', plain,
% 0.23/0.54      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.23/0.54        | (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.23/0.54        | (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.23/0.54        | (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('75', plain,
% 0.23/0.54      (((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.23/0.54       ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B)) | 
% 0.23/0.54       ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B))),
% 0.23/0.54      inference('split', [status(esa)], ['74'])).
% 0.23/0.54  thf('76', plain,
% 0.23/0.54      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.23/0.54       ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.54  thf('77', plain, ($false),
% 0.23/0.54      inference('sat_resolution*', [status(thm)],
% 0.23/0.54                ['1', '16', '18', '72', '49', '73', '75', '76'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
