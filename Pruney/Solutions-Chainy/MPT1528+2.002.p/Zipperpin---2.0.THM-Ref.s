%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6JZ3KikLL5

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:40 EST 2020

% Result     : Theorem 2.88s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  155 (1628 expanded)
%              Number of leaves         :   24 ( 454 expanded)
%              Depth                    :   22
%              Number of atoms          : 1235 (16489 expanded)
%              Number of equality atoms :   35 ( 405 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t6_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
              & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_yellow_0])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ ( sk_D_1 @ X19 @ X21 @ X20 ) @ X21 )
      | ( r2_lattice3 @ X20 @ X21 @ X19 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X17 @ X16 ) @ X17 )
      | ( r1_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( u1_orders_2 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_orders_2 @ X16 @ X15 @ ( sk_D @ X15 @ X17 @ X16 ) )
      | ( r1_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['44','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('61',plain,
    ( ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('62',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('65',plain,
    ( ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('66',plain,
    ( ! [X0: $i] :
        ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r1_lattice3 @ X0 @ X1 @ sk_B )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ~ ( r1_lattice3 @ X2 @ X1 @ X0 )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('71',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(simpl_trail,[status(thm)],['17','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_lattice3 @ X16 @ X17 @ X15 )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_orders_2 @ X16 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(simpl_trail,[status(thm)],['17','71'])).

thf('83',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['44','58'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_lattice3 @ sk_A @ X0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['74','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('88',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( ( sk_D_1 @ sk_B @ ( k1_tarski @ X0 ) @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ ( sk_D_1 @ X19 @ X21 @ X20 ) @ X19 )
      | ( r2_lattice3 @ X20 @ X21 @ X19 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    r2_lattice3 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_A @ X0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','97'])).

thf('99',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('100',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_lattice3 @ X20 @ X21 @ X19 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_orders_2 @ X20 @ X22 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
        | ~ ( r2_hidden @ sk_B @ X1 ) )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('111',plain,
    ( ! [X0: $i,X1: $i] :
        ( r2_hidden @ X1 @ X0 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
        | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['113','117'])).

thf('119',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('120',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('121',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('122',plain,
    ( ! [X0: $i] :
        ~ ( r2_lattice3 @ sk_A @ X0 @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r2_lattice3 @ X0 @ X1 @ sk_B )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['118','123'])).

thf('125',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r2_lattice3 @ sk_A @ X1 @ X0 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['112','124'])).

thf('126',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ~ ( r2_lattice3 @ X0 @ X2 @ X1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','125'])).

thf('127',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_lattice3 @ X0 @ X2 @ X1 ) ),
    inference(simpl_trail,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('sup-',[status(thm)],['98','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6JZ3KikLL5
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:43:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 2.88/3.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.88/3.13  % Solved by: fo/fo7.sh
% 2.88/3.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.88/3.13  % done 868 iterations in 2.666s
% 2.88/3.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.88/3.13  % SZS output start Refutation
% 2.88/3.13  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.88/3.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.88/3.13  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 2.88/3.13  thf(sk_B_type, type, sk_B: $i).
% 2.88/3.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.88/3.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.88/3.13  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 2.88/3.13  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 2.88/3.13  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 2.88/3.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.88/3.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.88/3.13  thf(sk_A_type, type, sk_A: $i).
% 2.88/3.13  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.88/3.13  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 2.88/3.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.88/3.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.88/3.13  thf(t6_yellow_0, conjecture,
% 2.88/3.13    (![A:$i]:
% 2.88/3.13     ( ( l1_orders_2 @ A ) =>
% 2.88/3.13       ( ![B:$i]:
% 2.88/3.13         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 2.88/3.13             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 2.88/3.13  thf(zf_stmt_0, negated_conjecture,
% 2.88/3.13    (~( ![A:$i]:
% 2.88/3.13        ( ( l1_orders_2 @ A ) =>
% 2.88/3.13          ( ![B:$i]:
% 2.88/3.13            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13              ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 2.88/3.13                ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ) )),
% 2.88/3.13    inference('cnf.neg', [status(esa)], [t6_yellow_0])).
% 2.88/3.13  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf(d9_lattice3, axiom,
% 2.88/3.13    (![A:$i]:
% 2.88/3.13     ( ( l1_orders_2 @ A ) =>
% 2.88/3.13       ( ![B:$i,C:$i]:
% 2.88/3.13         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 2.88/3.13             ( ![D:$i]:
% 2.88/3.13               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 2.88/3.13  thf('1', plain,
% 2.88/3.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 2.88/3.13          | (r2_hidden @ (sk_D_1 @ X19 @ X21 @ X20) @ X21)
% 2.88/3.13          | (r2_lattice3 @ X20 @ X21 @ X19)
% 2.88/3.13          | ~ (l1_orders_2 @ X20))),
% 2.88/3.13      inference('cnf', [status(esa)], [d9_lattice3])).
% 2.88/3.13  thf('2', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (l1_orders_2 @ sk_A)
% 2.88/3.13          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['0', '1'])).
% 2.88/3.13  thf('3', plain, ((l1_orders_2 @ sk_A)),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('4', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 2.88/3.13      inference('demod', [status(thm)], ['2', '3'])).
% 2.88/3.13  thf(t4_subset_1, axiom,
% 2.88/3.13    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.88/3.13  thf('5', plain,
% 2.88/3.13      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 2.88/3.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.88/3.13  thf(l3_subset_1, axiom,
% 2.88/3.13    (![A:$i,B:$i]:
% 2.88/3.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.88/3.13       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.88/3.13  thf('6', plain,
% 2.88/3.13      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.88/3.13         (~ (r2_hidden @ X5 @ X6)
% 2.88/3.13          | (r2_hidden @ X5 @ X7)
% 2.88/3.13          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 2.88/3.13      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.88/3.13  thf('7', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['5', '6'])).
% 2.88/3.13  thf('8', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A) @ X0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['4', '7'])).
% 2.88/3.13  thf(d1_tarski, axiom,
% 2.88/3.13    (![A:$i,B:$i]:
% 2.88/3.13     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.88/3.13       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.88/3.13  thf('9', plain,
% 2.88/3.13      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.88/3.13         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 2.88/3.13      inference('cnf', [status(esa)], [d1_tarski])).
% 2.88/3.13  thf('10', plain,
% 2.88/3.13      (![X0 : $i, X3 : $i]:
% 2.88/3.13         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.88/3.13      inference('simplify', [status(thm)], ['9'])).
% 2.88/3.13  thf('11', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['8', '10'])).
% 2.88/3.13  thf('12', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['8', '10'])).
% 2.88/3.13  thf('13', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         (((X0) = (X1))
% 2.88/3.13          | (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup+', [status(thm)], ['11', '12'])).
% 2.88/3.13  thf('14', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B) | ((X0) = (X1)))),
% 2.88/3.13      inference('simplify', [status(thm)], ['13'])).
% 2.88/3.13  thf('15', plain,
% 2.88/3.13      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13        | ~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('16', plain,
% 2.88/3.13      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('split', [status(esa)], ['15'])).
% 2.88/3.13  thf('17', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['14', '16'])).
% 2.88/3.13  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf(d8_lattice3, axiom,
% 2.88/3.13    (![A:$i]:
% 2.88/3.13     ( ( l1_orders_2 @ A ) =>
% 2.88/3.13       ( ![B:$i,C:$i]:
% 2.88/3.13         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 2.88/3.13             ( ![D:$i]:
% 2.88/3.13               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 2.88/3.13  thf('20', plain,
% 2.88/3.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 2.88/3.13          | (r2_hidden @ (sk_D @ X15 @ X17 @ X16) @ X17)
% 2.88/3.13          | (r1_lattice3 @ X16 @ X17 @ X15)
% 2.88/3.13          | ~ (l1_orders_2 @ X16))),
% 2.88/3.13      inference('cnf', [status(esa)], [d8_lattice3])).
% 2.88/3.13  thf('21', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (l1_orders_2 @ sk_A)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['19', '20'])).
% 2.88/3.13  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('23', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 2.88/3.13      inference('demod', [status(thm)], ['21', '22'])).
% 2.88/3.13  thf('24', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['5', '6'])).
% 2.88/3.13  thf('25', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ X0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['23', '24'])).
% 2.88/3.13  thf('26', plain,
% 2.88/3.13      (![X0 : $i, X3 : $i]:
% 2.88/3.13         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.88/3.13      inference('simplify', [status(thm)], ['9'])).
% 2.88/3.13  thf('27', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['25', '26'])).
% 2.88/3.13  thf('28', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ X0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['23', '24'])).
% 2.88/3.13  thf('29', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r2_hidden @ X0 @ X1)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup+', [status(thm)], ['27', '28'])).
% 2.88/3.13  thf('30', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B) | (r2_hidden @ X0 @ X1))),
% 2.88/3.13      inference('simplify', [status(thm)], ['29'])).
% 2.88/3.13  thf(d9_orders_2, axiom,
% 2.88/3.13    (![A:$i]:
% 2.88/3.13     ( ( l1_orders_2 @ A ) =>
% 2.88/3.13       ( ![B:$i]:
% 2.88/3.13         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13           ( ![C:$i]:
% 2.88/3.13             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.88/3.13               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 2.88/3.13                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 2.88/3.13  thf('31', plain,
% 2.88/3.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 2.88/3.13          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (u1_orders_2 @ X13))
% 2.88/3.13          | (r1_orders_2 @ X13 @ X12 @ X14)
% 2.88/3.13          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.88/3.13          | ~ (l1_orders_2 @ X13))),
% 2.88/3.13      inference('cnf', [status(esa)], [d9_orders_2])).
% 2.88/3.13  thf('32', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ~ (l1_orders_2 @ X0)
% 2.88/3.13          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.88/3.13          | (r1_orders_2 @ X0 @ X2 @ X1)
% 2.88/3.13          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['30', '31'])).
% 2.88/3.13  thf('33', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.88/3.13          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (l1_orders_2 @ sk_A)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['18', '32'])).
% 2.88/3.13  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('35', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.88/3.13          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('demod', [status(thm)], ['33', '34'])).
% 2.88/3.13  thf('36', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['25', '26'])).
% 2.88/3.13  thf('37', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0))),
% 2.88/3.13      inference('demod', [status(thm)], ['21', '22'])).
% 2.88/3.13  thf('38', plain,
% 2.88/3.13      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 2.88/3.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.88/3.13  thf(t4_subset, axiom,
% 2.88/3.13    (![A:$i,B:$i,C:$i]:
% 2.88/3.13     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.88/3.13       ( m1_subset_1 @ A @ C ) ))).
% 2.88/3.13  thf('39', plain,
% 2.88/3.13      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.88/3.13         (~ (r2_hidden @ X9 @ X10)
% 2.88/3.13          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.88/3.13          | (m1_subset_1 @ X9 @ X11))),
% 2.88/3.13      inference('cnf', [status(esa)], [t4_subset])).
% 2.88/3.13  thf('40', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['38', '39'])).
% 2.88/3.13  thf('41', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (m1_subset_1 @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ X0))),
% 2.88/3.13      inference('sup-', [status(thm)], ['37', '40'])).
% 2.88/3.13  thf('42', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((m1_subset_1 @ X0 @ X1)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup+', [status(thm)], ['36', '41'])).
% 2.88/3.13  thf('43', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B) | (m1_subset_1 @ X0 @ X1))),
% 2.88/3.13      inference('simplify', [status(thm)], ['42'])).
% 2.88/3.13  thf('44', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 2.88/3.13      inference('clc', [status(thm)], ['35', '43'])).
% 2.88/3.13  thf('45', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['25', '26'])).
% 2.88/3.13  thf('46', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['25', '26'])).
% 2.88/3.13  thf('47', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         (((X0) = (X1))
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup+', [status(thm)], ['45', '46'])).
% 2.88/3.13  thf('48', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B) | ((X0) = (X1)))),
% 2.88/3.13      inference('simplify', [status(thm)], ['47'])).
% 2.88/3.13  thf('49', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['25', '26'])).
% 2.88/3.13  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('51', plain,
% 2.88/3.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 2.88/3.13          | ~ (r1_orders_2 @ X16 @ X15 @ (sk_D @ X15 @ X17 @ X16))
% 2.88/3.13          | (r1_lattice3 @ X16 @ X17 @ X15)
% 2.88/3.13          | ~ (l1_orders_2 @ X16))),
% 2.88/3.13      inference('cnf', [status(esa)], [d8_lattice3])).
% 2.88/3.13  thf('52', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (l1_orders_2 @ sk_A)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['50', '51'])).
% 2.88/3.13  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('54', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ X0 @ sk_A)))),
% 2.88/3.13      inference('demod', [status(thm)], ['52', '53'])).
% 2.88/3.13  thf('55', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['49', '54'])).
% 2.88/3.13  thf('56', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 2.88/3.13      inference('simplify', [status(thm)], ['55'])).
% 2.88/3.13  thf('57', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         (~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['48', '56'])).
% 2.88/3.13  thf('58', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ X0 @ X1))),
% 2.88/3.13      inference('simplify', [status(thm)], ['57'])).
% 2.88/3.13  thf('59', plain, ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 2.88/3.13      inference('clc', [status(thm)], ['44', '58'])).
% 2.88/3.13  thf('60', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B) | ((X0) = (X1)))),
% 2.88/3.13      inference('simplify', [status(thm)], ['47'])).
% 2.88/3.13  thf('61', plain,
% 2.88/3.13      ((~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('split', [status(esa)], ['15'])).
% 2.88/3.13  thf('62', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['60', '61'])).
% 2.88/3.13  thf('63', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['60', '61'])).
% 2.88/3.13  thf('64', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['60', '61'])).
% 2.88/3.13  thf('65', plain,
% 2.88/3.13      ((~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('split', [status(esa)], ['15'])).
% 2.88/3.13  thf('66', plain,
% 2.88/3.13      ((![X0 : $i]: ~ (r1_lattice3 @ sk_A @ X0 @ sk_B))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['64', '65'])).
% 2.88/3.13  thf('67', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ~ (r1_lattice3 @ X0 @ X1 @ sk_B))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['63', '66'])).
% 2.88/3.13  thf('68', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i, X2 : $i]: ~ (r1_lattice3 @ X2 @ X1 @ X0))
% 2.88/3.13         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['62', '67'])).
% 2.88/3.13  thf('69', plain, (((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['59', '68'])).
% 2.88/3.13  thf('70', plain,
% 2.88/3.13      (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)) | 
% 2.88/3.13       ~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('split', [status(esa)], ['15'])).
% 2.88/3.13  thf('71', plain, (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 2.88/3.13  thf('72', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 2.88/3.13      inference('simpl_trail', [status(thm)], ['17', '71'])).
% 2.88/3.13  thf('73', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.13         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 2.88/3.13      inference('cnf', [status(esa)], [d1_tarski])).
% 2.88/3.13  thf('74', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.88/3.13      inference('simplify', [status(thm)], ['73'])).
% 2.88/3.13  thf('75', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('76', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('77', plain,
% 2.88/3.13      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 2.88/3.13          | ~ (r1_lattice3 @ X16 @ X17 @ X15)
% 2.88/3.13          | ~ (r2_hidden @ X18 @ X17)
% 2.88/3.13          | (r1_orders_2 @ X16 @ X15 @ X18)
% 2.88/3.13          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 2.88/3.13          | ~ (l1_orders_2 @ X16))),
% 2.88/3.13      inference('cnf', [status(esa)], [d8_lattice3])).
% 2.88/3.13  thf('78', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         (~ (l1_orders_2 @ sk_A)
% 2.88/3.13          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.88/3.13          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.88/3.13          | ~ (r2_hidden @ X0 @ X1)
% 2.88/3.13          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['76', '77'])).
% 2.88/3.13  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('80', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.88/3.13          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 2.88/3.13          | ~ (r2_hidden @ X0 @ X1)
% 2.88/3.13          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.88/3.13      inference('demod', [status(thm)], ['78', '79'])).
% 2.88/3.13  thf('81', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (r1_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r2_hidden @ sk_B @ X0)
% 2.88/3.13          | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['75', '80'])).
% 2.88/3.13  thf('82', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 2.88/3.13      inference('simpl_trail', [status(thm)], ['17', '71'])).
% 2.88/3.13  thf('83', plain, ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)),
% 2.88/3.13      inference('clc', [status(thm)], ['44', '58'])).
% 2.88/3.13  thf('84', plain, (![X0 : $i]: (r1_lattice3 @ sk_A @ X0 @ sk_B)),
% 2.88/3.13      inference('sup+', [status(thm)], ['82', '83'])).
% 2.88/3.13  thf('85', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (r2_hidden @ sk_B @ X0) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 2.88/3.13      inference('demod', [status(thm)], ['81', '84'])).
% 2.88/3.13  thf('86', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 2.88/3.13      inference('sup-', [status(thm)], ['74', '85'])).
% 2.88/3.13  thf('87', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0))),
% 2.88/3.13      inference('demod', [status(thm)], ['2', '3'])).
% 2.88/3.13  thf('88', plain,
% 2.88/3.13      (![X0 : $i, X3 : $i]:
% 2.88/3.13         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.88/3.13      inference('simplify', [status(thm)], ['9'])).
% 2.88/3.13  thf('89', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 2.88/3.13          | ((sk_D_1 @ sk_B @ (k1_tarski @ X0) @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['87', '88'])).
% 2.88/3.13  thf('90', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('91', plain,
% 2.88/3.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 2.88/3.13          | ~ (r1_orders_2 @ X20 @ (sk_D_1 @ X19 @ X21 @ X20) @ X19)
% 2.88/3.13          | (r2_lattice3 @ X20 @ X21 @ X19)
% 2.88/3.13          | ~ (l1_orders_2 @ X20))),
% 2.88/3.13      inference('cnf', [status(esa)], [d9_lattice3])).
% 2.88/3.13  thf('92', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (l1_orders_2 @ sk_A)
% 2.88/3.13          | (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['90', '91'])).
% 2.88/3.13  thf('93', plain, ((l1_orders_2 @ sk_A)),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('94', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 2.88/3.13      inference('demod', [status(thm)], ['92', '93'])).
% 2.88/3.13  thf('95', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 2.88/3.13          | (r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['89', '94'])).
% 2.88/3.13  thf('96', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ (k1_tarski @ X0) @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 2.88/3.13      inference('simplify', [status(thm)], ['95'])).
% 2.88/3.13  thf('97', plain, ((r2_lattice3 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)),
% 2.88/3.13      inference('sup-', [status(thm)], ['86', '96'])).
% 2.88/3.13  thf('98', plain, (![X0 : $i]: (r2_lattice3 @ sk_A @ X0 @ sk_B)),
% 2.88/3.13      inference('sup+', [status(thm)], ['72', '97'])).
% 2.88/3.13  thf('99', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['14', '16'])).
% 2.88/3.13  thf('100', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['14', '16'])).
% 2.88/3.13  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('102', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('103', plain,
% 2.88/3.13      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 2.88/3.13          | ~ (r2_lattice3 @ X20 @ X21 @ X19)
% 2.88/3.13          | ~ (r2_hidden @ X22 @ X21)
% 2.88/3.13          | (r1_orders_2 @ X20 @ X22 @ X19)
% 2.88/3.13          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 2.88/3.13          | ~ (l1_orders_2 @ X20))),
% 2.88/3.13      inference('cnf', [status(esa)], [d9_lattice3])).
% 2.88/3.13  thf('104', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         (~ (l1_orders_2 @ sk_A)
% 2.88/3.13          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.88/3.13          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r2_hidden @ X0 @ X1)
% 2.88/3.13          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['102', '103'])).
% 2.88/3.13  thf('105', plain, ((l1_orders_2 @ sk_A)),
% 2.88/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.13  thf('106', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i]:
% 2.88/3.13         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.88/3.13          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r2_hidden @ X0 @ X1)
% 2.88/3.13          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_B))),
% 2.88/3.13      inference('demod', [status(thm)], ['104', '105'])).
% 2.88/3.13  thf('107', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r2_hidden @ sk_B @ X0)
% 2.88/3.13          | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['101', '106'])).
% 2.88/3.13  thf('108', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]:
% 2.88/3.13          (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 2.88/3.13           | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 2.88/3.13           | ~ (r2_hidden @ sk_B @ X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['100', '107'])).
% 2.88/3.13  thf('109', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['14', '16'])).
% 2.88/3.13  thf('110', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.88/3.13      inference('simplify', [status(thm)], ['73'])).
% 2.88/3.13  thf('111', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ X0))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup+', [status(thm)], ['109', '110'])).
% 2.88/3.13  thf('112', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]:
% 2.88/3.13          (~ (r2_lattice3 @ sk_A @ X1 @ X0)
% 2.88/3.13           | (r1_orders_2 @ sk_A @ sk_B @ sk_B)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('demod', [status(thm)], ['108', '111'])).
% 2.88/3.13  thf('113', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['14', '16'])).
% 2.88/3.13  thf('114', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ((sk_D_1 @ sk_B @ k1_xboole_0 @ sk_A) = (X0)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['8', '10'])).
% 2.88/3.13  thf('115', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_B))),
% 2.88/3.13      inference('demod', [status(thm)], ['92', '93'])).
% 2.88/3.13  thf('116', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         (~ (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 2.88/3.13          | (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sup-', [status(thm)], ['114', '115'])).
% 2.88/3.13  thf('117', plain,
% 2.88/3.13      (![X0 : $i]:
% 2.88/3.13         ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)
% 2.88/3.13          | ~ (r1_orders_2 @ sk_A @ X0 @ sk_B))),
% 2.88/3.13      inference('simplify', [status(thm)], ['116'])).
% 2.88/3.13  thf('118', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]:
% 2.88/3.13          (~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 2.88/3.13           | (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['113', '117'])).
% 2.88/3.13  thf('119', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['14', '16'])).
% 2.88/3.13  thf('120', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['14', '16'])).
% 2.88/3.13  thf('121', plain,
% 2.88/3.13      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('split', [status(esa)], ['15'])).
% 2.88/3.13  thf('122', plain,
% 2.88/3.13      ((![X0 : $i]: ~ (r2_lattice3 @ sk_A @ X0 @ sk_B))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['120', '121'])).
% 2.88/3.13  thf('123', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ~ (r2_lattice3 @ X0 @ X1 @ sk_B))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['119', '122'])).
% 2.88/3.13  thf('124', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ~ (r1_orders_2 @ sk_A @ X1 @ X0))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('clc', [status(thm)], ['118', '123'])).
% 2.88/3.13  thf('125', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i]: ~ (r2_lattice3 @ sk_A @ X1 @ X0))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('clc', [status(thm)], ['112', '124'])).
% 2.88/3.13  thf('126', plain,
% 2.88/3.13      ((![X0 : $i, X1 : $i, X2 : $i]: ~ (r2_lattice3 @ X0 @ X2 @ X1))
% 2.88/3.13         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 2.88/3.13      inference('sup-', [status(thm)], ['99', '125'])).
% 2.88/3.13  thf('127', plain, (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B))),
% 2.88/3.13      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 2.88/3.13  thf('128', plain,
% 2.88/3.13      (![X0 : $i, X1 : $i, X2 : $i]: ~ (r2_lattice3 @ X0 @ X2 @ X1)),
% 2.88/3.13      inference('simpl_trail', [status(thm)], ['126', '127'])).
% 2.88/3.13  thf('129', plain, ($false), inference('sup-', [status(thm)], ['98', '128'])).
% 2.88/3.13  
% 2.88/3.13  % SZS output end Refutation
% 2.88/3.13  
% 2.98/3.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
