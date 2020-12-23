%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IowC6OrPZ0

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 160 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  814 (2263 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

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
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
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
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X12 @ X11 ) @ X12 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
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
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X10 @ X12 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_orders_2 @ X11 @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ ( sk_D_1 @ X10 @ X12 @ X11 ) @ X10 )
      | ( r2_lattice3 @ X11 @ X12 @ X10 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('38',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('42',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('49',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X8 @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_orders_2 @ X7 @ X6 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_orders_2 @ X7 @ X6 @ ( sk_D @ X6 @ X8 @ X7 ) )
      | ( r1_lattice3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['62','67'])).

thf('69',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['42','68'])).

thf('70',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('71',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','40','41','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IowC6OrPZ0
% 0.11/0.33  % Computer   : n001.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:21:45 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running portfolio for 600 s
% 0.11/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 70 iterations in 0.035s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.48  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.20/0.48  thf(t9_yellow_0, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( r1_tarski @ B @ C ) =>
% 0.20/0.48           ( ![D:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.20/0.48                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_orders_2 @ A ) =>
% 0.20/0.48          ( ![B:$i,C:$i]:
% 0.20/0.48            ( ( r1_tarski @ B @ C ) =>
% 0.20/0.48              ( ![D:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                  ( ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.20/0.48                      ( r1_lattice3 @ A @ B @ D ) ) & 
% 0.20/0.48                    ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.20/0.48                      ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t9_yellow_0])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.20/0.48        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.20/0.48       ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.20/0.48       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.20/0.48        | ~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.20/0.48       ~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('split', [status(esa)], ['4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.20/0.48         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.20/0.48      inference('split', [status(esa)], ['6'])).
% 0.20/0.48  thf('8', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d9_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.20/0.48             ( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.48          | (r2_hidden @ (sk_D_1 @ X10 @ X12 @ X11) @ X12)
% 0.20/0.48          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.20/0.48          | ~ (l1_orders_2 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t3_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X3 : $i, X5 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(l3_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | (r2_hidden @ X0 @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '17'])).
% 0.20/0.48  thf('19', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.48          | (m1_subset_1 @ (sk_D_1 @ X10 @ X12 @ X11) @ (u1_struct_0 @ X11))
% 0.20/0.48          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.20/0.48          | ~ (l1_orders_2 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.48          | ~ (r2_lattice3 @ X11 @ X12 @ X10)
% 0.20/0.48          | ~ (r2_hidden @ X13 @ X12)
% 0.20/0.48          | (r1_orders_2 @ X11 @ X13 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.20/0.48          | ~ (l1_orders_2 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.20/0.48          | ~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.20/0.48          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.20/0.48        | ~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.20/0.48        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.20/0.48        | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_D_2)
% 0.20/0.48        | (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.48  thf('32', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.48          | ~ (r1_orders_2 @ X11 @ (sk_D_1 @ X10 @ X12 @ X11) @ X10)
% 0.20/0.48          | (r2_lattice3 @ X11 @ X12 @ X10)
% 0.20/0.48          | ~ (l1_orders_2 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | ~ (r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.48         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((~ (r2_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.48         <= (~ ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.20/0.48       ((r2_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.20/0.48       ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.20/0.48      inference('split', [status(esa)], ['6'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.20/0.48         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.20/0.48      inference('split', [status(esa)], ['4'])).
% 0.20/0.48  thf('43', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d8_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i,C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.20/0.48             ( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.20/0.48          | (r1_lattice3 @ X7 @ X8 @ X6)
% 0.20/0.48          | ~ (l1_orders_2 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_B @ sk_A) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ X6 @ X8 @ X7) @ (u1_struct_0 @ X7))
% 0.20/0.48          | (r1_lattice3 @ X7 @ X8 @ X6)
% 0.20/0.48          | ~ (l1_orders_2 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (r1_lattice3 @ X7 @ X8 @ X6)
% 0.20/0.48          | ~ (r2_hidden @ X9 @ X8)
% 0.20/0.48          | (r1_orders_2 @ X7 @ X6 @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (l1_orders_2 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.20/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.20/0.48          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 0.20/0.48          | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['54', '59'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.20/0.48        | ~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.20/0.48        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['49', '60'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      ((~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.20/0.48        | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B @ sk_A))
% 0.20/0.48        | (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))),
% 0.20/0.48      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.48  thf('63', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.20/0.48          | ~ (r1_orders_2 @ X7 @ X6 @ (sk_D @ X6 @ X8 @ X7))
% 0.20/0.48          | (r1_lattice3 @ X7 @ X8 @ X6)
% 0.20/0.48          | ~ (l1_orders_2 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_A)
% 0.20/0.48          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.48  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.20/0.48          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)
% 0.20/0.48        | ~ (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.20/0.48      inference('clc', [status(thm)], ['62', '67'])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.48         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '68'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      ((~ (r1_lattice3 @ sk_A @ sk_B @ sk_D_2))
% 0.20/0.48         <= (~ ((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      (((r1_lattice3 @ sk_A @ sk_B @ sk_D_2)) | 
% 0.20/0.48       ~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.48  thf('72', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)],
% 0.20/0.48                ['1', '3', '5', '40', '41', '71'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
