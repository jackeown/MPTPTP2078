%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PREMx84iZm

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:42 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 173 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  954 (3605 expanded)
%              Number of equality atoms :   19 (  42 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X11 @ X13 @ X12 ) @ X13 )
      | ( r2_lattice3 @ X12 @ X13 @ X11 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( ( sk_D_2 @ sk_B @ ( k1_tarski @ X0 ) @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_orders_2 @ X12 @ ( sk_D_2 @ X11 @ X13 @ X12 ) @ X11 )
      | ( r2_lattice3 @ X12 @ X13 @ X11 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_lattice3 @ X12 @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_orders_2 @ X12 @ X14 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
      | ~ ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ) )
   <= ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('38',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','39'])).

thf('41',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
   <= ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_orders_2 @ X8 @ X7 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ~ ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ) )
   <= ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('53',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('55',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('57',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X9 @ X8 ) @ X9 )
      | ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( ( sk_D_1 @ sk_B @ ( k1_tarski @ X0 ) @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ ( sk_D_1 @ X7 @ X9 @ X8 ) )
      | ( r1_lattice3 @ X8 @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','73'])).

thf('75',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_lattice3 @ sk_A @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','26','42','55','56','58','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PREMx84iZm
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 194 iterations in 0.146s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.42/0.60  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.60  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.42/0.60  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(t7_yellow_0, conjecture,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_orders_2 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60           ( ![C:$i]:
% 0.42/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60               ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.42/0.60                   ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.42/0.60                 ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.42/0.60                   ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.42/0.60                 ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.42/0.60                   ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.42/0.60                 ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.42/0.60                   ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]:
% 0.42/0.60        ( ( l1_orders_2 @ A ) =>
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60              ( ![C:$i]:
% 0.42/0.60                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60                  ( ( ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.42/0.60                      ( r1_orders_2 @ A @ B @ C ) ) & 
% 0.42/0.60                    ( ( r1_orders_2 @ A @ B @ C ) =>
% 0.42/0.60                      ( r1_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) & 
% 0.42/0.60                    ( ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) =>
% 0.42/0.60                      ( r1_orders_2 @ A @ C @ B ) ) & 
% 0.42/0.60                    ( ( r1_orders_2 @ A @ C @ B ) =>
% 0.42/0.60                      ( r2_lattice3 @ A @ ( k1_tarski @ C ) @ B ) ) ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t7_yellow_0])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)
% 0.42/0.60        | (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.42/0.60        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.42/0.60        | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.42/0.60       ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)) | 
% 0.42/0.60       ~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)) | 
% 0.42/0.60       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.42/0.60        | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)
% 0.42/0.60        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.42/0.60        | ~ (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.42/0.60       ~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)) | 
% 0.42/0.60       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 0.42/0.60       ~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.42/0.60        | ~ (r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)
% 0.42/0.60        | (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)
% 0.42/0.60        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.42/0.60         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['4'])).
% 0.42/0.60  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(d9_lattice3, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_orders_2 @ A ) =>
% 0.42/0.60       ( ![B:$i,C:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.42/0.60             ( ![D:$i]:
% 0.42/0.60               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.42/0.60          | (r2_hidden @ (sk_D_2 @ X11 @ X13 @ X12) @ X13)
% 0.42/0.60          | (r2_lattice3 @ X12 @ X13 @ X11)
% 0.42/0.60          | ~ (l1_orders_2 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_orders_2 @ sk_A)
% 0.42/0.60          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | (r2_hidden @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.60  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | (r2_hidden @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf(t69_enumset1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.60  thf('11', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.60  thf(d2_tarski, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.42/0.60       ( ![D:$i]:
% 0.42/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.42/0.60          | ((X4) = (X3))
% 0.42/0.60          | ((X4) = (X0))
% 0.42/0.60          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (((X4) = (X0))
% 0.42/0.60          | ((X4) = (X3))
% 0.42/0.60          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.42/0.60          | ((sk_D_2 @ sk_B @ (k1_tarski @ X0) @ sk_A) = (X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '15'])).
% 0.42/0.60  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.42/0.60          | ~ (r1_orders_2 @ X12 @ (sk_D_2 @ X11 @ X13 @ X12) @ X11)
% 0.42/0.60          | (r2_lattice3 @ X12 @ X13 @ X11)
% 0.42/0.60          | ~ (l1_orders_2 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_orders_2 @ sk_A)
% 0.42/0.60          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r1_orders_2 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r1_orders_2 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.42/0.60          | (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '21'])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.42/0.60          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 0.42/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))
% 0.42/0.60         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      ((~ (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))
% 0.42/0.60         <= (~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 0.42/0.60       ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))
% 0.42/0.60         <= (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['4'])).
% 0.42/0.60  thf('28', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('29', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.42/0.60          | ~ (r2_lattice3 @ X12 @ X13 @ X11)
% 0.42/0.60          | ~ (r2_hidden @ X14 @ X13)
% 0.42/0.60          | (r1_orders_2 @ X12 @ X14 @ X11)
% 0.42/0.60          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.42/0.60          | ~ (l1_orders_2 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (l1_orders_2 @ sk_A)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.42/0.60          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.60  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.42/0.60          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r2_hidden @ sk_C @ X0)
% 0.42/0.60          | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      ((((r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.42/0.60         | ~ (r2_hidden @ sk_C @ (k1_tarski @ sk_C))))
% 0.42/0.60         <= (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '34'])).
% 0.42/0.60  thf('36', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.60         (((X1) != (X0))
% 0.42/0.60          | (r2_hidden @ X1 @ X2)
% 0.42/0.60          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.60  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['36', '38'])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.42/0.60         <= (((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('demod', [status(thm)], ['35', '39'])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 0.42/0.60         <= (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (~ ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)) | 
% 0.42/0.60       ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))
% 0.42/0.60         <= (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('44', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(d8_lattice3, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_orders_2 @ A ) =>
% 0.42/0.60       ( ![B:$i,C:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.42/0.60             ( ![D:$i]:
% 0.42/0.60               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.42/0.60          | ~ (r1_lattice3 @ X8 @ X9 @ X7)
% 0.42/0.60          | ~ (r2_hidden @ X10 @ X9)
% 0.42/0.60          | (r1_orders_2 @ X8 @ X7 @ X10)
% 0.42/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.42/0.60          | ~ (l1_orders_2 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (l1_orders_2 @ sk_A)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.42/0.60          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.60  thf('48', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.42/0.60          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r2_hidden @ sk_C @ X0)
% 0.42/0.60          | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.42/0.60      inference('sup-', [status(thm)], ['44', '49'])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      ((((r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.42/0.60         | ~ (r2_hidden @ sk_C @ (k1_tarski @ sk_C))))
% 0.42/0.60         <= (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['43', '50'])).
% 0.42/0.60  thf('52', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['36', '38'])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.42/0.60         <= (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('demod', [status(thm)], ['51', '52'])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.42/0.60         <= (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.42/0.60       ~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.42/0.60       ~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)) | 
% 0.42/0.60       ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 0.42/0.60       ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('split', [status(esa)], ['4'])).
% 0.42/0.60  thf('57', plain,
% 0.42/0.60      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)
% 0.42/0.60        | (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.42/0.60        | (r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)
% 0.42/0.60        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.42/0.60       ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)) | 
% 0.42/0.60       ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 0.42/0.60       ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('split', [status(esa)], ['57'])).
% 0.42/0.60  thf('59', plain,
% 0.42/0.60      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.42/0.60         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('60', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('61', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.42/0.60          | (r2_hidden @ (sk_D_1 @ X7 @ X9 @ X8) @ X9)
% 0.42/0.60          | (r1_lattice3 @ X8 @ X9 @ X7)
% 0.42/0.60          | ~ (l1_orders_2 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_orders_2 @ sk_A)
% 0.42/0.60          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.60  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('64', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['62', '63'])).
% 0.42/0.60  thf('65', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.42/0.60  thf('66', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.42/0.60          | ((sk_D_1 @ sk_B @ (k1_tarski @ X0) @ sk_A) = (X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.60  thf('67', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('68', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.42/0.60          | ~ (r1_orders_2 @ X8 @ X7 @ (sk_D_1 @ X7 @ X9 @ X8))
% 0.42/0.60          | (r1_lattice3 @ X8 @ X9 @ X7)
% 0.42/0.60          | ~ (l1_orders_2 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.42/0.60  thf('69', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_orders_2 @ sk_A)
% 0.42/0.60          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.60  thf('70', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('71', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 0.42/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['69', '70'])).
% 0.42/0.60  thf('72', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.42/0.60          | (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.42/0.60          | (r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['66', '71'])).
% 0.42/0.60  thf('73', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 0.42/0.60          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['72'])).
% 0.42/0.60  thf('74', plain,
% 0.42/0.60      (((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))
% 0.42/0.60         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['59', '73'])).
% 0.42/0.60  thf('75', plain,
% 0.42/0.60      ((~ (r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))
% 0.42/0.60         <= (~ ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('76', plain,
% 0.42/0.60      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.42/0.60       ((r1_lattice3 @ sk_A @ (k1_tarski @ sk_C) @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['74', '75'])).
% 0.42/0.60  thf('77', plain, ($false),
% 0.42/0.60      inference('sat_resolution*', [status(thm)],
% 0.42/0.60                ['1', '3', '26', '42', '55', '56', '58', '76'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
