%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MLjoUTI3tz

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:42 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 269 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          : 1659 (8893 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(t8_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B )
                     => ( ( r1_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ B @ D ) ) )
                    & ( ( ( r1_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ B @ D ) )
                     => ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) )
                    & ( ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B )
                     => ( ( r1_orders_2 @ A @ C @ B )
                        & ( r1_orders_2 @ A @ D @ B ) ) )
                    & ( ( ( r1_orders_2 @ A @ C @ B )
                        & ( r1_orders_2 @ A @ D @ B ) )
                     => ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B )
                       => ( ( r1_orders_2 @ A @ B @ C )
                          & ( r1_orders_2 @ A @ B @ D ) ) )
                      & ( ( ( r1_orders_2 @ A @ B @ C )
                          & ( r1_orders_2 @ A @ B @ D ) )
                       => ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) )
                      & ( ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B )
                       => ( ( r1_orders_2 @ A @ C @ B )
                          & ( r1_orders_2 @ A @ D @ B ) ) )
                      & ( ( ( r1_orders_2 @ A @ C @ B )
                          & ( r1_orders_2 @ A @ D @ B ) )
                       => ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_yellow_0])).

thf('0',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_orders_2 @ X11 @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_D_3 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_tarski @ sk_C @ sk_D_3 ) ) )
   <= ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','18'])).

thf('20',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('24',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D_2 @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k2_tarski @ X1 @ X0 ) @ sk_B )
      | ( ( sk_D_2 @ sk_B @ ( k2_tarski @ X1 @ X0 ) @ sk_A )
        = X1 )
      | ( ( sk_D_2 @ sk_B @ ( k2_tarski @ X1 @ X0 ) @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ ( sk_D_2 @ X10 @ X12 @ X11 ) @ X10 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( ( sk_D_2 @ sk_B @ ( k2_tarski @ X0 @ X1 ) @ sk_A )
        = X1 )
      | ( r2_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_B )
      | ( ( sk_D_2 @ sk_B @ ( k2_tarski @ X0 @ X1 ) @ sk_A )
        = X1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_B @ ( k2_tarski @ sk_C @ X0 ) @ sk_A )
          = X0 )
        | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
        | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B )
        | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
      & ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','44'])).

thf('46',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('47',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('51',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
      | ~ ( r2_hidden @ sk_C @ ( k2_tarski @ sk_C @ sk_D_3 ) ) )
   <= ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('59',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','59'])).

thf('61',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('62',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_orders_2 @ X7 @ X6 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_D_3 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_tarski @ sk_C @ sk_D_3 ) ) )
   <= ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('73',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
   <= ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['20'])).

thf('75',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('77',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['48'])).

thf('78',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['51'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X6 @ X8 @ X7 ) @ X8 )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ X1 @ X0 ) @ sk_B )
      | ( ( sk_D_1 @ sk_B @ ( k2_tarski @ X1 @ X0 ) @ sk_A )
        = X1 )
      | ( ( sk_D_1 @ sk_B @ ( k2_tarski @ X1 @ X0 ) @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_orders_2 @ X7 @ X6 @ ( sk_D_1 @ X6 @ X8 @ X7 ) )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( ( sk_D_1 @ sk_B @ ( k2_tarski @ X0 @ X1 ) @ sk_A )
        = X1 )
      | ( r1_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_B )
      | ( r1_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ X0 @ X1 ) @ sk_B )
      | ( ( sk_D_1 @ sk_B @ ( k2_tarski @ X0 @ X1 ) @ sk_A )
        = X1 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_1 @ sk_B @ ( k2_tarski @ sk_C @ X0 ) @ sk_A )
          = X0 )
        | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
        | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B )
        | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ X0 ) @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) )
   <= ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['77','96'])).

thf('98',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('99',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_3 )
    | ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
   <= ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_C @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
      | ~ ( r2_hidden @ sk_C @ ( k2_tarski @ sk_C @ sk_D_3 ) ) )
   <= ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('106',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('108',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_tarski @ sk_C @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','22','47','49','50','52','62','75','76','99','108','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MLjoUTI3tz
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.62/2.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.62/2.85  % Solved by: fo/fo7.sh
% 2.62/2.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.62/2.85  % done 6673 iterations in 2.388s
% 2.62/2.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.62/2.85  % SZS output start Refutation
% 2.62/2.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.62/2.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.62/2.85  thf(sk_B_type, type, sk_B: $i).
% 2.62/2.85  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 2.62/2.85  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 2.62/2.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.62/2.85  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 2.62/2.85  thf(sk_D_3_type, type, sk_D_3: $i).
% 2.62/2.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.62/2.85  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.62/2.85  thf(sk_A_type, type, sk_A: $i).
% 2.62/2.85  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 2.62/2.85  thf(sk_C_type, type, sk_C: $i).
% 2.62/2.85  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 2.62/2.85  thf(t8_yellow_0, conjecture,
% 2.62/2.85    (![A:$i]:
% 2.62/2.85     ( ( l1_orders_2 @ A ) =>
% 2.62/2.85       ( ![B:$i]:
% 2.62/2.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85           ( ![C:$i]:
% 2.62/2.85             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85               ( ![D:$i]:
% 2.62/2.85                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85                   ( ( ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) =>
% 2.62/2.85                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 2.62/2.85                         ( r1_orders_2 @ A @ B @ D ) ) ) & 
% 2.62/2.85                     ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 2.62/2.85                         ( r1_orders_2 @ A @ B @ D ) ) =>
% 2.62/2.85                       ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) & 
% 2.62/2.85                     ( ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) =>
% 2.62/2.85                       ( ( r1_orders_2 @ A @ C @ B ) & 
% 2.62/2.85                         ( r1_orders_2 @ A @ D @ B ) ) ) & 
% 2.62/2.85                     ( ( ( r1_orders_2 @ A @ C @ B ) & 
% 2.62/2.85                         ( r1_orders_2 @ A @ D @ B ) ) =>
% 2.62/2.85                       ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) ) ) ) ) ) ) ) ))).
% 2.62/2.85  thf(zf_stmt_0, negated_conjecture,
% 2.62/2.85    (~( ![A:$i]:
% 2.62/2.85        ( ( l1_orders_2 @ A ) =>
% 2.62/2.85          ( ![B:$i]:
% 2.62/2.85            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85              ( ![C:$i]:
% 2.62/2.85                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85                  ( ![D:$i]:
% 2.62/2.85                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85                      ( ( ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) =>
% 2.62/2.85                          ( ( r1_orders_2 @ A @ B @ C ) & 
% 2.62/2.85                            ( r1_orders_2 @ A @ B @ D ) ) ) & 
% 2.62/2.85                        ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 2.62/2.85                            ( r1_orders_2 @ A @ B @ D ) ) =>
% 2.62/2.85                          ( r1_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) & 
% 2.62/2.85                        ( ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) =>
% 2.62/2.85                          ( ( r1_orders_2 @ A @ C @ B ) & 
% 2.62/2.85                            ( r1_orders_2 @ A @ D @ B ) ) ) & 
% 2.62/2.85                        ( ( ( r1_orders_2 @ A @ C @ B ) & 
% 2.62/2.85                            ( r1_orders_2 @ A @ D @ B ) ) =>
% 2.62/2.85                          ( r2_lattice3 @ A @ ( k2_tarski @ C @ D ) @ B ) ) ) ) ) ) ) ) ) ) )),
% 2.62/2.85    inference('cnf.neg', [status(esa)], [t8_yellow_0])).
% 2.62/2.85  thf('0', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_B @ sk_D_3)
% 2.62/2.85        | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('1', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 2.62/2.85       ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))),
% 2.62/2.85      inference('split', [status(esa)], ['0'])).
% 2.62/2.85  thf('2', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 2.62/2.85        | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('3', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 2.62/2.85       ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('split', [status(esa)], ['2'])).
% 2.62/2.85  thf('4', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_B @ sk_D_3)
% 2.62/2.85        | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('5', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('split', [status(esa)], ['4'])).
% 2.62/2.85  thf('6', plain,
% 2.62/2.85      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D_3)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 2.62/2.85        | ~ (r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('7', plain,
% 2.62/2.85      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)) | 
% 2.62/2.85       ~ ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 2.62/2.85      inference('split', [status(esa)], ['6'])).
% 2.62/2.85  thf('8', plain,
% 2.62/2.85      (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['6'])).
% 2.62/2.85  thf('9', plain, ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf(d9_lattice3, axiom,
% 2.62/2.85    (![A:$i]:
% 2.62/2.85     ( ( l1_orders_2 @ A ) =>
% 2.62/2.85       ( ![B:$i,C:$i]:
% 2.62/2.85         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 2.62/2.85             ( ![D:$i]:
% 2.62/2.85               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 2.62/2.85  thf('11', plain,
% 2.62/2.85      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 2.62/2.85          | ~ (r2_lattice3 @ X11 @ X12 @ X10)
% 2.62/2.85          | ~ (r2_hidden @ X13 @ X12)
% 2.62/2.85          | (r1_orders_2 @ X11 @ X13 @ X10)
% 2.62/2.85          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.62/2.85          | ~ (l1_orders_2 @ X11))),
% 2.62/2.85      inference('cnf', [status(esa)], [d9_lattice3])).
% 2.62/2.85  thf('12', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (l1_orders_2 @ sk_A)
% 2.62/2.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.62/2.85          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r2_hidden @ X0 @ X1)
% 2.62/2.85          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['10', '11'])).
% 2.62/2.85  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('14', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.62/2.85          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r2_hidden @ X0 @ X1)
% 2.62/2.85          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.62/2.85      inference('demod', [status(thm)], ['12', '13'])).
% 2.62/2.85  thf('15', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r2_hidden @ sk_D_3 @ X0)
% 2.62/2.85          | (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['9', '14'])).
% 2.62/2.85  thf('16', plain,
% 2.62/2.85      ((((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)
% 2.62/2.85         | ~ (r2_hidden @ sk_D_3 @ (k2_tarski @ sk_C @ sk_D_3))))
% 2.62/2.85         <= (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['8', '15'])).
% 2.62/2.85  thf(d2_tarski, axiom,
% 2.62/2.85    (![A:$i,B:$i,C:$i]:
% 2.62/2.85     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.62/2.85       ( ![D:$i]:
% 2.62/2.85         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.62/2.85  thf('17', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.62/2.85         (((X1) != (X0))
% 2.62/2.85          | (r2_hidden @ X1 @ X2)
% 2.62/2.85          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.62/2.85      inference('cnf', [status(esa)], [d2_tarski])).
% 2.62/2.85  thf('18', plain,
% 2.62/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 2.62/2.85      inference('simplify', [status(thm)], ['17'])).
% 2.62/2.85  thf('19', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))
% 2.62/2.85         <= (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('demod', [status(thm)], ['16', '18'])).
% 2.62/2.85  thf('20', plain,
% 2.62/2.85      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D_3)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 2.62/2.85        | ~ (r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 2.62/2.85        | ~ (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('21', plain,
% 2.62/2.85      ((~ (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))
% 2.62/2.85         <= (~ ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['20'])).
% 2.62/2.85  thf('22', plain,
% 2.62/2.85      (~ ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['19', '21'])).
% 2.62/2.85  thf('23', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['6'])).
% 2.62/2.85  thf('24', plain,
% 2.62/2.85      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D_3)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 2.62/2.85        | ~ (r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('25', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['24'])).
% 2.62/2.85  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('27', plain,
% 2.62/2.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 2.62/2.85          | (r2_hidden @ (sk_D_2 @ X10 @ X12 @ X11) @ X12)
% 2.62/2.85          | (r2_lattice3 @ X11 @ X12 @ X10)
% 2.62/2.85          | ~ (l1_orders_2 @ X11))),
% 2.62/2.85      inference('cnf', [status(esa)], [d9_lattice3])).
% 2.62/2.85  thf('28', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (l1_orders_2 @ sk_A)
% 2.62/2.85          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | (r2_hidden @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0))),
% 2.62/2.85      inference('sup-', [status(thm)], ['26', '27'])).
% 2.62/2.85  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('30', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | (r2_hidden @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0))),
% 2.62/2.85      inference('demod', [status(thm)], ['28', '29'])).
% 2.62/2.85  thf('31', plain,
% 2.62/2.85      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.62/2.85         (~ (r2_hidden @ X4 @ X2)
% 2.62/2.85          | ((X4) = (X3))
% 2.62/2.85          | ((X4) = (X0))
% 2.62/2.85          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.62/2.85      inference('cnf', [status(esa)], [d2_tarski])).
% 2.62/2.85  thf('32', plain,
% 2.62/2.85      (![X0 : $i, X3 : $i, X4 : $i]:
% 2.62/2.85         (((X4) = (X0))
% 2.62/2.85          | ((X4) = (X3))
% 2.62/2.85          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 2.62/2.85      inference('simplify', [status(thm)], ['31'])).
% 2.62/2.85  thf('33', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         ((r2_lattice3 @ sk_A @ (k2_tarski @ X1 @ X0) @ sk_B)
% 2.62/2.85          | ((sk_D_2 @ sk_B @ (k2_tarski @ X1 @ X0) @ sk_A) = (X1))
% 2.62/2.85          | ((sk_D_2 @ sk_B @ (k2_tarski @ X1 @ X0) @ sk_A) = (X0)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['30', '32'])).
% 2.62/2.85  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('35', plain,
% 2.62/2.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 2.62/2.85          | ~ (r1_orders_2 @ X11 @ (sk_D_2 @ X10 @ X12 @ X11) @ X10)
% 2.62/2.85          | (r2_lattice3 @ X11 @ X12 @ X10)
% 2.62/2.85          | ~ (l1_orders_2 @ X11))),
% 2.62/2.85      inference('cnf', [status(esa)], [d9_lattice3])).
% 2.62/2.85  thf('36', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (l1_orders_2 @ sk_A)
% 2.62/2.85          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['34', '35'])).
% 2.62/2.85  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('38', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 2.62/2.85      inference('demod', [status(thm)], ['36', '37'])).
% 2.62/2.85  thf('39', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ((sk_D_2 @ sk_B @ (k2_tarski @ X0 @ X1) @ sk_A) = (X1))
% 2.62/2.85          | (r2_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_B)
% 2.62/2.85          | (r2_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['33', '38'])).
% 2.62/2.85  thf('40', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         ((r2_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_B)
% 2.62/2.85          | ((sk_D_2 @ sk_B @ (k2_tarski @ X0 @ X1) @ sk_A) = (X1))
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 2.62/2.85      inference('simplify', [status(thm)], ['39'])).
% 2.62/2.85  thf('41', plain,
% 2.62/2.85      ((![X0 : $i]:
% 2.62/2.85          (((sk_D_2 @ sk_B @ (k2_tarski @ sk_C @ X0) @ sk_A) = (X0))
% 2.62/2.85           | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['25', '40'])).
% 2.62/2.85  thf('42', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 2.62/2.85      inference('demod', [status(thm)], ['36', '37'])).
% 2.62/2.85  thf('43', plain,
% 2.62/2.85      ((![X0 : $i]:
% 2.62/2.85          (~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.62/2.85           | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)
% 2.62/2.85           | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['41', '42'])).
% 2.62/2.85  thf('44', plain,
% 2.62/2.85      ((![X0 : $i]:
% 2.62/2.85          ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)
% 2.62/2.85           | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B)))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 2.62/2.85      inference('simplify', [status(thm)], ['43'])).
% 2.62/2.85  thf('45', plain,
% 2.62/2.85      (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_B)) & 
% 2.62/2.85             ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['23', '44'])).
% 2.62/2.85  thf('46', plain,
% 2.62/2.85      ((~ (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (~ ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['20'])).
% 2.62/2.85  thf('47', plain,
% 2.62/2.85      (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 2.62/2.85       ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['45', '46'])).
% 2.62/2.85  thf('48', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_B @ sk_D_3)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 2.62/2.85        | ~ (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('49', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('split', [status(esa)], ['48'])).
% 2.62/2.85  thf('50', plain,
% 2.62/2.85      (~ ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ~ ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 2.62/2.85      inference('split', [status(esa)], ['20'])).
% 2.62/2.85  thf('51', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_D_3 @ sk_B)
% 2.62/2.85        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 2.62/2.85        | ~ (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('52', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_D_3 @ sk_B))),
% 2.62/2.85      inference('split', [status(esa)], ['51'])).
% 2.62/2.85  thf('53', plain,
% 2.62/2.85      (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['6'])).
% 2.62/2.85  thf('54', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('55', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.62/2.85          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r2_hidden @ X0 @ X1)
% 2.62/2.85          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.62/2.85      inference('demod', [status(thm)], ['12', '13'])).
% 2.62/2.85  thf('56', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r2_hidden @ sk_C @ X0)
% 2.62/2.85          | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['54', '55'])).
% 2.62/2.85  thf('57', plain,
% 2.62/2.85      ((((r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 2.62/2.85         | ~ (r2_hidden @ sk_C @ (k2_tarski @ sk_C @ sk_D_3))))
% 2.62/2.85         <= (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['53', '56'])).
% 2.62/2.85  thf('58', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.62/2.85         (((X1) != (X3))
% 2.62/2.85          | (r2_hidden @ X1 @ X2)
% 2.62/2.85          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.62/2.85      inference('cnf', [status(esa)], [d2_tarski])).
% 2.62/2.85  thf('59', plain,
% 2.62/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 2.62/2.85      inference('simplify', [status(thm)], ['58'])).
% 2.62/2.85  thf('60', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 2.62/2.85         <= (((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('demod', [status(thm)], ['57', '59'])).
% 2.62/2.85  thf('61', plain,
% 2.62/2.85      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))
% 2.62/2.85         <= (~ ((r1_orders_2 @ sk_A @ sk_C @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['20'])).
% 2.62/2.85  thf('62', plain,
% 2.62/2.85      (~ ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['60', '61'])).
% 2.62/2.85  thf('63', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['51'])).
% 2.62/2.85  thf('64', plain, ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('65', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf(d8_lattice3, axiom,
% 2.62/2.85    (![A:$i]:
% 2.62/2.85     ( ( l1_orders_2 @ A ) =>
% 2.62/2.85       ( ![B:$i,C:$i]:
% 2.62/2.85         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 2.62/2.85             ( ![D:$i]:
% 2.62/2.85               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.62/2.85                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 2.62/2.85  thf('66', plain,
% 2.62/2.85      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 2.62/2.85          | ~ (r1_lattice3 @ X7 @ X8 @ X6)
% 2.62/2.85          | ~ (r2_hidden @ X9 @ X8)
% 2.62/2.85          | (r1_orders_2 @ X7 @ X6 @ X9)
% 2.62/2.85          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 2.62/2.85          | ~ (l1_orders_2 @ X7))),
% 2.62/2.85      inference('cnf', [status(esa)], [d8_lattice3])).
% 2.62/2.85  thf('67', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (l1_orders_2 @ sk_A)
% 2.62/2.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.62/2.85          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.62/2.85          | ~ (r2_hidden @ X0 @ X1)
% 2.62/2.85          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['65', '66'])).
% 2.62/2.85  thf('68', plain, ((l1_orders_2 @ sk_A)),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('69', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.62/2.85          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.62/2.85          | ~ (r2_hidden @ X0 @ X1)
% 2.62/2.85          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.62/2.85      inference('demod', [status(thm)], ['67', '68'])).
% 2.62/2.85  thf('70', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r2_hidden @ sk_D_3 @ X0)
% 2.62/2.85          | (r1_orders_2 @ sk_A @ sk_B @ sk_D_3))),
% 2.62/2.85      inference('sup-', [status(thm)], ['64', '69'])).
% 2.62/2.85  thf('71', plain,
% 2.62/2.85      ((((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)
% 2.62/2.85         | ~ (r2_hidden @ sk_D_3 @ (k2_tarski @ sk_C @ sk_D_3))))
% 2.62/2.85         <= (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['63', '70'])).
% 2.62/2.85  thf('72', plain,
% 2.62/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 2.62/2.85      inference('simplify', [status(thm)], ['17'])).
% 2.62/2.85  thf('73', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_D_3))
% 2.62/2.85         <= (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('demod', [status(thm)], ['71', '72'])).
% 2.62/2.85  thf('74', plain,
% 2.62/2.85      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_D_3))
% 2.62/2.85         <= (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)))),
% 2.62/2.85      inference('split', [status(esa)], ['20'])).
% 2.62/2.85  thf('75', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ~ ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['73', '74'])).
% 2.62/2.85  thf('76', plain,
% 2.62/2.85      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ~ ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 2.62/2.85       ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 2.62/2.85      inference('split', [status(esa)], ['24'])).
% 2.62/2.85  thf('77', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_D_3))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)))),
% 2.62/2.85      inference('split', [status(esa)], ['48'])).
% 2.62/2.85  thf('78', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 2.62/2.85      inference('split', [status(esa)], ['51'])).
% 2.62/2.85  thf('79', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('80', plain,
% 2.62/2.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 2.62/2.85          | (r2_hidden @ (sk_D_1 @ X6 @ X8 @ X7) @ X8)
% 2.62/2.85          | (r1_lattice3 @ X7 @ X8 @ X6)
% 2.62/2.85          | ~ (l1_orders_2 @ X7))),
% 2.62/2.85      inference('cnf', [status(esa)], [d8_lattice3])).
% 2.62/2.85  thf('81', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (l1_orders_2 @ sk_A)
% 2.62/2.85          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 2.62/2.85      inference('sup-', [status(thm)], ['79', '80'])).
% 2.62/2.85  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('83', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 2.62/2.85      inference('demod', [status(thm)], ['81', '82'])).
% 2.62/2.85  thf('84', plain,
% 2.62/2.85      (![X0 : $i, X3 : $i, X4 : $i]:
% 2.62/2.85         (((X4) = (X0))
% 2.62/2.85          | ((X4) = (X3))
% 2.62/2.85          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 2.62/2.85      inference('simplify', [status(thm)], ['31'])).
% 2.62/2.85  thf('85', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         ((r1_lattice3 @ sk_A @ (k2_tarski @ X1 @ X0) @ sk_B)
% 2.62/2.85          | ((sk_D_1 @ sk_B @ (k2_tarski @ X1 @ X0) @ sk_A) = (X1))
% 2.62/2.85          | ((sk_D_1 @ sk_B @ (k2_tarski @ X1 @ X0) @ sk_A) = (X0)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['83', '84'])).
% 2.62/2.85  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('87', plain,
% 2.62/2.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 2.62/2.85          | ~ (r1_orders_2 @ X7 @ X6 @ (sk_D_1 @ X6 @ X8 @ X7))
% 2.62/2.85          | (r1_lattice3 @ X7 @ X8 @ X6)
% 2.62/2.85          | ~ (l1_orders_2 @ X7))),
% 2.62/2.85      inference('cnf', [status(esa)], [d8_lattice3])).
% 2.62/2.85  thf('88', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (l1_orders_2 @ sk_A)
% 2.62/2.85          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['86', '87'])).
% 2.62/2.85  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('90', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 2.62/2.85      inference('demod', [status(thm)], ['88', '89'])).
% 2.62/2.85  thf('91', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.62/2.85          | ((sk_D_1 @ sk_B @ (k2_tarski @ X0 @ X1) @ sk_A) = (X1))
% 2.62/2.85          | (r1_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_B)
% 2.62/2.85          | (r1_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_B))),
% 2.62/2.85      inference('sup-', [status(thm)], ['85', '90'])).
% 2.62/2.85  thf('92', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         ((r1_lattice3 @ sk_A @ (k2_tarski @ X0 @ X1) @ sk_B)
% 2.62/2.85          | ((sk_D_1 @ sk_B @ (k2_tarski @ X0 @ X1) @ sk_A) = (X1))
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 2.62/2.85      inference('simplify', [status(thm)], ['91'])).
% 2.62/2.85  thf('93', plain,
% 2.62/2.85      ((![X0 : $i]:
% 2.62/2.85          (((sk_D_1 @ sk_B @ (k2_tarski @ sk_C @ X0) @ sk_A) = (X0))
% 2.62/2.85           | (r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['78', '92'])).
% 2.62/2.85  thf('94', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ X0 @ sk_A)))),
% 2.62/2.85      inference('demod', [status(thm)], ['88', '89'])).
% 2.62/2.85  thf('95', plain,
% 2.62/2.85      ((![X0 : $i]:
% 2.62/2.85          (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.62/2.85           | (r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)
% 2.62/2.85           | (r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['93', '94'])).
% 2.62/2.85  thf('96', plain,
% 2.62/2.85      ((![X0 : $i]:
% 2.62/2.85          ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ X0) @ sk_B)
% 2.62/2.85           | ~ (r1_orders_2 @ sk_A @ sk_B @ X0)))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 2.62/2.85      inference('simplify', [status(thm)], ['95'])).
% 2.62/2.85  thf('97', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (((r1_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 2.62/2.85             ((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['77', '96'])).
% 2.62/2.85  thf('98', plain,
% 2.62/2.85      ((~ (r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (~ ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['20'])).
% 2.62/2.85  thf('99', plain,
% 2.62/2.85      (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_D_3)) | 
% 2.62/2.85       ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 2.62/2.85      inference('sup-', [status(thm)], ['97', '98'])).
% 2.62/2.85  thf('100', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))
% 2.62/2.85         <= (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('split', [status(esa)], ['51'])).
% 2.62/2.85  thf('101', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('102', plain,
% 2.62/2.85      (![X0 : $i, X1 : $i]:
% 2.62/2.85         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.62/2.85          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.62/2.85          | ~ (r2_hidden @ X0 @ X1)
% 2.62/2.85          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.62/2.85      inference('demod', [status(thm)], ['67', '68'])).
% 2.62/2.85  thf('103', plain,
% 2.62/2.85      (![X0 : $i]:
% 2.62/2.85         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.62/2.85          | ~ (r2_hidden @ sk_C @ X0)
% 2.62/2.85          | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 2.62/2.85      inference('sup-', [status(thm)], ['101', '102'])).
% 2.62/2.85  thf('104', plain,
% 2.62/2.85      ((((r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 2.62/2.85         | ~ (r2_hidden @ sk_C @ (k2_tarski @ sk_C @ sk_D_3))))
% 2.62/2.85         <= (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('sup-', [status(thm)], ['100', '103'])).
% 2.62/2.85  thf('105', plain,
% 2.62/2.85      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 2.62/2.85      inference('simplify', [status(thm)], ['58'])).
% 2.62/2.85  thf('106', plain,
% 2.62/2.85      (((r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 2.62/2.85         <= (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)))),
% 2.62/2.85      inference('demod', [status(thm)], ['104', '105'])).
% 2.62/2.85  thf('107', plain,
% 2.62/2.85      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C))
% 2.62/2.85         <= (~ ((r1_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 2.62/2.85      inference('split', [status(esa)], ['20'])).
% 2.62/2.85  thf('108', plain,
% 2.62/2.85      (~ ((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 2.62/2.85      inference('sup-', [status(thm)], ['106', '107'])).
% 2.62/2.85  thf('109', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 2.62/2.85        | (r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)
% 2.62/2.85        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 2.62/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.62/2.85  thf('110', plain,
% 2.62/2.85      (((r1_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 2.62/2.85       ((r1_orders_2 @ sk_A @ sk_C @ sk_B)) | 
% 2.62/2.85       ((r2_lattice3 @ sk_A @ (k2_tarski @ sk_C @ sk_D_3) @ sk_B))),
% 2.62/2.85      inference('split', [status(esa)], ['109'])).
% 2.62/2.85  thf('111', plain, ($false),
% 2.62/2.85      inference('sat_resolution*', [status(thm)],
% 2.62/2.85                ['1', '3', '5', '7', '22', '47', '49', '50', '52', '62', '75', 
% 2.62/2.85                 '76', '99', '108', '110'])).
% 2.62/2.85  
% 2.62/2.85  % SZS output end Refutation
% 2.62/2.85  
% 2.62/2.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
