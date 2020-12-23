%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B64YYQOChp

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:50 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 294 expanded)
%              Number of leaves         :   23 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          : 1492 (6275 expanded)
%              Number of equality atoms :    9 ( 118 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t63_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( E = D )
                       => ( ( ( r1_lattice3 @ B @ C @ E )
                           => ( r1_lattice3 @ A @ C @ D ) )
                          & ( ( r2_lattice3 @ B @ C @ E )
                           => ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_yellow_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ( ( E = D )
                         => ( ( ( r1_lattice3 @ B @ C @ E )
                             => ( r1_lattice3 @ A @ C @ D ) )
                            & ( ( r2_lattice3 @ B @ C @ E )
                             => ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_yellow_0])).

thf('0',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
    | ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
   <= ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    sk_E = sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_E = sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_B @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_yellow_0 @ X8 @ X9 )
      | ( l1_orders_2 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('27',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_B @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ( ( ( E = C )
                              & ( F = D )
                              & ( r1_orders_2 @ B @ E @ F ) )
                           => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_yellow_0 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ X17 @ X16 )
      | ( X16 != X15 )
      | ( r1_orders_2 @ X14 @ X18 @ X15 )
      | ( X17 != X18 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t60_yellow_0])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X14 @ X18 @ X15 )
      | ~ ( r1_orders_2 @ X13 @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_yellow_0 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ sk_D_2 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X1 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ sk_D_2 @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X1 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( r1_orders_2 @ X1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_yellow_0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( m1_yellow_0 @ sk_B @ sk_A )
    | ~ ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('51',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) )
      | ( r1_lattice3 @ X1 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['52','57'])).

thf('59',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['34','58'])).

thf('60',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['6'])).

thf('64',plain,
    ( ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
   <= ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['4'])).

thf('65',plain,(
    sk_E = sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X6 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('74',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('76',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_orders_2 @ X5 @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_B @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_B @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['71','80'])).

thf('82',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
    | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['66','82'])).

thf('84',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('85',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X13: $i,X14: $i,X15: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X14 @ X18 @ X15 )
      | ~ ( r1_orders_2 @ X13 @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_yellow_0 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_yellow_0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( m1_yellow_0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X2 )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_yellow_0 @ sk_B @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['83','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('100',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X5 @ ( sk_D_1 @ X4 @ X6 @ X5 ) @ X4 )
      | ( r2_lattice3 @ X5 @ X6 @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['102','107'])).

thf('109',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('110',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','62','63','110'])).


%------------------------------------------------------------------------------
