%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sAOuRtd4U

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 153 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  794 (2223 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t9_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ C @ D )
                 => ( r1_lattice3 @ A @ B @ D ) )
                & ( ( r2_lattice3 @ A @ C @ D )
                 => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( ( r1_lattice3 @ A @ C @ D )
                   => ( r1_lattice3 @ A @ B @ D ) )
                  & ( ( r2_lattice3 @ A @ C @ D )
                   => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_yellow_0])).

thf('0',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X10 @ X9 ) @ X10 )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X8 @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_orders_2 @ X9 @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_orders_2 @ X9 @ ( sk_D_1 @ X8 @ X10 @ X9 ) @ X8 )
      | ( r2_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('40',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('47',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_orders_2 @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ X4 @ ( sk_D @ X4 @ X6 @ X5 ) )
      | ( r1_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['60','65'])).

thf('67',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['40','66'])).

thf('68',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','38','39','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sAOuRtd4U
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 70 iterations in 0.038s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(t9_yellow_0, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( ![B:$i,C:$i]:
% 0.20/0.50         ( ( r1_tarski @ B @ C ) =>
% 0.20/0.50           ( ![D:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.20/0.50                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( l1_orders_2 @ A ) =>
% 0.20/0.50          ( ![B:$i,C:$i]:
% 0.20/0.50            ( ( r1_tarski @ B @ C ) =>
% 0.20/0.50              ( ![D:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                  ( ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.20/0.50                      ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.20/0.50                    ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.20/0.50                      ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t9_yellow_0])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 0.20/0.50        | (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)) | 
% 0.20/0.50       ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.20/0.50       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 0.20/0.50        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)) | 
% 0.20/0.50       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))
% 0.20/0.50         <= (((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('8', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d9_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( ![B:$i,C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.20/0.50             ( ![D:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.50          | (r2_hidden @ (sk_D_1 @ X8 @ X10 @ X9) @ X10)
% 0.20/0.50          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.20/0.50          | ~ (l1_orders_2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.50  thf('17', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.50          | (m1_subset_1 @ (sk_D_1 @ X8 @ X10 @ X9) @ (u1_struct_0 @ X9))
% 0.20/0.50          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.20/0.50          | ~ (l1_orders_2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (r2_lattice3 @ X9 @ X10 @ X8)
% 0.20/0.50          | ~ (r2_hidden @ X11 @ X10)
% 0.20/0.50          | (r1_orders_2 @ X9 @ X11 @ X8)
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (l1_orders_2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.20/0.50          | ~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.20/0.50          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.20/0.50        | ~ (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 0.20/0.50        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 0.20/0.50        | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.20/0.50        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf('30', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (r1_orders_2 @ X9 @ (sk_D_1 @ X8 @ X10 @ X9) @ X8)
% 0.20/0.50          | (r2_lattice3 @ X9 @ X10 @ X8)
% 0.20/0.50          | ~ (l1_orders_2 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | ~ (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 0.20/0.50      inference('clc', [status(thm)], ['29', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.50         <= (((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.50         <= (~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (~ ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)) | 
% 0.20/0.50       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.20/0.50       ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))
% 0.20/0.50         <= (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('41', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d8_lattice3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_orders_2 @ A ) =>
% 0.20/0.50       ( ![B:$i,C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.20/0.50             ( ![D:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 0.20/0.50          | (r1_lattice3 @ X5 @ X6 @ X4)
% 0.20/0.50          | ~ (l1_orders_2 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ (u1_struct_0 @ X5))
% 0.20/0.50          | (r1_lattice3 @ X5 @ X6 @ X4)
% 0.20/0.50          | ~ (l1_orders_2 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (r1_lattice3 @ X5 @ X6 @ X4)
% 0.20/0.50          | ~ (r2_hidden @ X7 @ X6)
% 0.20/0.50          | (r1_orders_2 @ X5 @ X4 @ X7)
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (l1_orders_2 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.20/0.50          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.20/0.50          | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.20/0.50        | ~ (r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 0.20/0.50        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((~ (r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 0.20/0.50        | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.20/0.50        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.50  thf('61', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.20/0.50          | ~ (r1_orders_2 @ X5 @ X4 @ (sk_D @ X4 @ X6 @ X5))
% 0.20/0.50          | (r1_lattice3 @ X5 @ X6 @ X4)
% 0.20/0.50          | ~ (l1_orders_2 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.50          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.50        | ~ (r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 0.20/0.50      inference('clc', [status(thm)], ['60', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.50         <= (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.50         <= (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.20/0.50       ~ ((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.50  thf('70', plain, ($false),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['1', '3', '5', '38', '39', '69'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
