%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ztMXbrXOeY

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  172 (2763 expanded)
%              Number of leaves         :   25 ( 743 expanded)
%              Depth                    :   39
%              Number of atoms          : 1762 (56771 expanded)
%              Number of equality atoms :   38 (3349 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(t2_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i,D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ! [E: $i] :
                    ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                   => ( ( D = E )
                     => ( ( ( r2_lattice3 @ A @ C @ D )
                         => ( r2_lattice3 @ B @ C @ E ) )
                        & ( ( r1_lattice3 @ A @ C @ D )
                         => ( r1_lattice3 @ B @ C @ E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
             => ! [C: $i,D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( D = E )
                       => ( ( ( r2_lattice3 @ A @ C @ D )
                           => ( r2_lattice3 @ B @ C @ E ) )
                          & ( ( r1_lattice3 @ A @ C @ D )
                           => ( r1_lattice3 @ B @ C @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow_0])).

thf('0',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_D_2 = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_orders_2 @ X6 @ X7 )
       != ( g1_orders_2 @ X4 @ X5 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('18',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_orders_2 @ X6 @ X7 )
       != ( g1_orders_2 @ X4 @ X5 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('25',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('29',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ X14 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( r2_lattice3 @ sk_B @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X0 )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_orders_2 @ X13 @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ sk_D_2 )
      | ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['30','46'])).

thf('48',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
   <= ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    sk_D_2 = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['48'])).

thf('53',plain,
    ( ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E )
    | ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['53'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

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

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ( r1_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ X0 )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( r1_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_orders_2 @ X9 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) )
      | ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['55','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('80',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) ) @ ( u1_orders_2 @ sk_A ) )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) ) @ ( u1_orders_2 @ sk_A ) )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['87','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('100',plain,
    ( ( ( r1_orders_2 @ sk_B @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_B ) )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('102',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_orders_2 @ X9 @ X8 @ ( sk_D @ X8 @ X10 @ X9 ) )
      | ( r1_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ ( sk_D @ X0 @ X1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ ( sk_D @ X0 @ X1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
   <= ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['48'])).

thf('111',plain,(
    sk_D_2 = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['52','54','113'])).

thf('115',plain,(
    ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['51','114'])).

thf('116',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['47','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B @ X0 @ sk_D_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['51','114'])).

thf('126',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('128',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['28','130'])).

thf('132',plain,(
    ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['51','114'])).

thf('133',plain,
    ( ( r1_orders_2 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['26'])).

thf('135',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( r2_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D_1 @ X0 @ X1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D_1 @ X0 @ X1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
      | ~ ( m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( r2_lattice3 @ sk_B @ sk_C @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['51','114'])).

thf('143',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r1_lattice3 @ sk_B @ sk_C @ sk_E )
    | ( r2_lattice3 @ sk_A @ sk_C @ sk_D_2 ) ),
    inference(split,[status(esa)],['29'])).

thf('145',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','143','144','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ztMXbrXOeY
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.61  % Solved by: fo/fo7.sh
% 0.21/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.61  % done 209 iterations in 0.158s
% 0.21/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.61  % SZS output start Refutation
% 0.21/0.61  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.61  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.61  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.61  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.61  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.21/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.61  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.61  thf(t2_yellow_0, conjecture,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( l1_orders_2 @ A ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( l1_orders_2 @ B ) =>
% 0.21/0.61           ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.21/0.61               ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) =>
% 0.21/0.61             ( ![C:$i,D:$i]:
% 0.21/0.61               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.61                 ( ![E:$i]:
% 0.21/0.61                   ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.61                     ( ( ( D ) = ( E ) ) =>
% 0.21/0.61                       ( ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.61                           ( r2_lattice3 @ B @ C @ E ) ) & 
% 0.21/0.61                         ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.21/0.61                           ( r1_lattice3 @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.61    (~( ![A:$i]:
% 0.21/0.61        ( ( l1_orders_2 @ A ) =>
% 0.21/0.61          ( ![B:$i]:
% 0.21/0.61            ( ( l1_orders_2 @ B ) =>
% 0.21/0.61              ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.21/0.61                  ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) =>
% 0.21/0.61                ( ![C:$i,D:$i]:
% 0.21/0.61                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.61                    ( ![E:$i]:
% 0.21/0.61                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.61                        ( ( ( D ) = ( E ) ) =>
% 0.21/0.61                          ( ( ( r2_lattice3 @ A @ C @ D ) =>
% 0.21/0.61                              ( r2_lattice3 @ B @ C @ E ) ) & 
% 0.21/0.61                            ( ( r1_lattice3 @ A @ C @ D ) =>
% 0.21/0.61                              ( r1_lattice3 @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.61    inference('cnf.neg', [status(esa)], [t2_yellow_0])).
% 0.21/0.61  thf('0', plain,
% 0.21/0.61      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.21/0.61        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('1', plain,
% 0.21/0.61      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.21/0.61       ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.21/0.61      inference('split', [status(esa)], ['0'])).
% 0.21/0.61  thf('2', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('3', plain, (((sk_D_2) = (sk_E))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('4', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_B))),
% 0.21/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.61  thf(d9_lattice3, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( l1_orders_2 @ A ) =>
% 0.21/0.61       ( ![B:$i,C:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.61           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.21/0.61             ( ![D:$i]:
% 0.21/0.61               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.61                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.21/0.61  thf('5', plain,
% 0.21/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.61          | (m1_subset_1 @ (sk_D_1 @ X12 @ X14 @ X13) @ (u1_struct_0 @ X13))
% 0.21/0.61          | (r2_lattice3 @ X13 @ X14 @ X12)
% 0.21/0.61          | ~ (l1_orders_2 @ X13))),
% 0.21/0.61      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.21/0.61  thf('6', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (l1_orders_2 @ sk_B)
% 0.21/0.61          | (r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.21/0.61          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.61  thf('7', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('8', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.21/0.61          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.61  thf('9', plain,
% 0.21/0.61      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.61         = (g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf(dt_u1_orders_2, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( l1_orders_2 @ A ) =>
% 0.21/0.61       ( m1_subset_1 @
% 0.21/0.61         ( u1_orders_2 @ A ) @ 
% 0.21/0.61         ( k1_zfmisc_1 @
% 0.21/0.61           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.61  thf('10', plain,
% 0.21/0.61      (![X3 : $i]:
% 0.21/0.61         ((m1_subset_1 @ (u1_orders_2 @ X3) @ 
% 0.21/0.61           (k1_zfmisc_1 @ 
% 0.21/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X3))))
% 0.21/0.61          | ~ (l1_orders_2 @ X3))),
% 0.21/0.61      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.61  thf(free_g1_orders_2, axiom,
% 0.21/0.61    (![A:$i,B:$i]:
% 0.21/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.21/0.61       ( ![C:$i,D:$i]:
% 0.21/0.61         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.21/0.61           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.61  thf('11', plain,
% 0.21/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.61         (((g1_orders_2 @ X6 @ X7) != (g1_orders_2 @ X4 @ X5))
% 0.21/0.61          | ((X7) = (X5))
% 0.21/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X6))))),
% 0.21/0.61      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.21/0.61  thf('12', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.61         (~ (l1_orders_2 @ X0)
% 0.21/0.61          | ((u1_orders_2 @ X0) = (X1))
% 0.21/0.61          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.21/0.61              != (g1_orders_2 @ X2 @ X1)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.61  thf('13', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.61            != (g1_orders_2 @ X1 @ X0))
% 0.21/0.61          | ((u1_orders_2 @ sk_B) = (X0))
% 0.21/0.61          | ~ (l1_orders_2 @ sk_B))),
% 0.21/0.61      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.61  thf('14', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('15', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.61            != (g1_orders_2 @ X1 @ X0))
% 0.21/0.61          | ((u1_orders_2 @ sk_B) = (X0)))),
% 0.21/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.61  thf('16', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_A))),
% 0.21/0.61      inference('eq_res', [status(thm)], ['15'])).
% 0.21/0.61  thf('17', plain,
% 0.21/0.61      (![X3 : $i]:
% 0.21/0.61         ((m1_subset_1 @ (u1_orders_2 @ X3) @ 
% 0.21/0.61           (k1_zfmisc_1 @ 
% 0.21/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X3))))
% 0.21/0.61          | ~ (l1_orders_2 @ X3))),
% 0.21/0.61      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.61  thf('18', plain,
% 0.21/0.61      (((m1_subset_1 @ (u1_orders_2 @ sk_A) @ 
% 0.21/0.61         (k1_zfmisc_1 @ 
% 0.21/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))))
% 0.21/0.61        | ~ (l1_orders_2 @ sk_B))),
% 0.21/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.61  thf('19', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('20', plain,
% 0.21/0.61      ((m1_subset_1 @ (u1_orders_2 @ sk_A) @ 
% 0.21/0.61        (k1_zfmisc_1 @ 
% 0.21/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.61  thf('21', plain,
% 0.21/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.61         (((g1_orders_2 @ X6 @ X7) != (g1_orders_2 @ X4 @ X5))
% 0.21/0.61          | ((X6) = (X4))
% 0.21/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X6))))),
% 0.21/0.61      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.21/0.61  thf('22', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (((u1_struct_0 @ sk_B) = (X0))
% 0.21/0.61          | ((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_A))
% 0.21/0.61              != (g1_orders_2 @ X0 @ X1)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.61  thf('23', plain,
% 0.21/0.61      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.61         = (g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B)))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('24', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_A))),
% 0.21/0.61      inference('eq_res', [status(thm)], ['15'])).
% 0.21/0.61  thf('25', plain,
% 0.21/0.61      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.61         = (g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.61  thf('26', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (((u1_struct_0 @ sk_B) = (X0))
% 0.21/0.61          | ((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.61              != (g1_orders_2 @ X0 @ X1)))),
% 0.21/0.61      inference('demod', [status(thm)], ['22', '25'])).
% 0.21/0.61  thf('27', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.21/0.61  thf('28', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.21/0.61          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('demod', [status(thm)], ['8', '27'])).
% 0.21/0.61  thf('29', plain,
% 0.21/0.61      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)
% 0.21/0.61        | ~ (r1_lattice3 @ sk_B @ sk_C @ sk_E))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('30', plain,
% 0.21/0.61      (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.21/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.21/0.61      inference('split', [status(esa)], ['29'])).
% 0.21/0.61  thf('31', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('32', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.21/0.61  thf('33', plain,
% 0.21/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.61          | (r2_hidden @ (sk_D_1 @ X12 @ X14 @ X13) @ X14)
% 0.21/0.61          | (r2_lattice3 @ X13 @ X14 @ X12)
% 0.21/0.61          | ~ (l1_orders_2 @ X13))),
% 0.21/0.61      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.21/0.61  thf('34', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (l1_orders_2 @ sk_B)
% 0.21/0.61          | (r2_lattice3 @ sk_B @ X1 @ X0)
% 0.21/0.61          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ sk_B) @ X1))),
% 0.21/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.61  thf('35', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('36', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | (r2_lattice3 @ sk_B @ X1 @ X0)
% 0.21/0.61          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ sk_B) @ X1))),
% 0.21/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.61  thf('37', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ X0)
% 0.21/0.61          | (r2_lattice3 @ sk_B @ X0 @ sk_D_2))),
% 0.21/0.61      inference('sup-', [status(thm)], ['31', '36'])).
% 0.21/0.61  thf('38', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.21/0.61          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('demod', [status(thm)], ['8', '27'])).
% 0.21/0.61  thf('39', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.44/0.61          | ~ (r2_lattice3 @ X13 @ X14 @ X12)
% 0.44/0.61          | ~ (r2_hidden @ X15 @ X14)
% 0.44/0.61          | (r1_orders_2 @ X13 @ X15 @ X12)
% 0.44/0.61          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.44/0.61          | ~ (l1_orders_2 @ X13))),
% 0.44/0.61      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (l1_orders_2 @ sk_A)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.44/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.44/0.61          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.61  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 0.44/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.44/0.61          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.44/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.61  thf('44', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.44/0.61          | ~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ X1)
% 0.44/0.61          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['38', '43'])).
% 0.44/0.61  thf('45', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_D_2)
% 0.44/0.61          | ~ (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.44/0.61          | (r2_lattice3 @ sk_B @ X0 @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['37', '44'])).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.44/0.61          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ sk_D_2)
% 0.44/0.61          | (r2_lattice3 @ sk_B @ X0 @ sk_D_2))),
% 0.44/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.61  thf('47', plain,
% 0.44/0.61      ((((r2_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2)))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '46'])).
% 0.44/0.61  thf('48', plain,
% 0.44/0.61      ((~ (r2_lattice3 @ sk_B @ sk_C @ sk_E)
% 0.44/0.61        | ~ (r1_lattice3 @ sk_B @ sk_C @ sk_E))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('49', plain,
% 0.44/0.61      ((~ (r2_lattice3 @ sk_B @ sk_C @ sk_E))
% 0.44/0.61         <= (~ ((r2_lattice3 @ sk_B @ sk_C @ sk_E)))),
% 0.44/0.61      inference('split', [status(esa)], ['48'])).
% 0.44/0.61  thf('50', plain, (((sk_D_2) = (sk_E))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('51', plain,
% 0.44/0.61      ((~ (r2_lattice3 @ sk_B @ sk_C @ sk_D_2))
% 0.44/0.61         <= (~ ((r2_lattice3 @ sk_B @ sk_C @ sk_E)))),
% 0.44/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.61  thf('52', plain,
% 0.44/0.61      (~ ((r2_lattice3 @ sk_B @ sk_C @ sk_E)) | 
% 0.44/0.61       ~ ((r1_lattice3 @ sk_B @ sk_C @ sk_E))),
% 0.44/0.61      inference('split', [status(esa)], ['48'])).
% 0.44/0.61  thf('53', plain,
% 0.44/0.61      ((~ (r2_lattice3 @ sk_B @ sk_C @ sk_E)
% 0.44/0.61        | (r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('54', plain,
% 0.44/0.61      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)) | 
% 0.44/0.61       ~ ((r2_lattice3 @ sk_B @ sk_C @ sk_E))),
% 0.44/0.61      inference('split', [status(esa)], ['53'])).
% 0.44/0.61  thf('55', plain,
% 0.44/0.61      (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('split', [status(esa)], ['53'])).
% 0.44/0.61  thf('56', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('57', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.44/0.61  thf(d8_lattice3, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_orders_2 @ A ) =>
% 0.44/0.61       ( ![B:$i,C:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.61           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.44/0.61             ( ![D:$i]:
% 0.44/0.61               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.61                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf('58', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.44/0.61          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.44/0.61          | (r1_lattice3 @ X9 @ X10 @ X8)
% 0.44/0.61          | ~ (l1_orders_2 @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.44/0.61  thf('59', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | ~ (l1_orders_2 @ sk_B)
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X1 @ X0)
% 0.44/0.61          | (r2_hidden @ (sk_D @ X0 @ X1 @ sk_B) @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.61  thf('60', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('61', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X1 @ X0)
% 0.44/0.61          | (r2_hidden @ (sk_D @ X0 @ X1 @ sk_B) @ X1))),
% 0.44/0.61      inference('demod', [status(thm)], ['59', '60'])).
% 0.44/0.61  thf('62', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_B) @ X0)
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X0 @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['56', '61'])).
% 0.44/0.61  thf('63', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_B))),
% 0.44/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.44/0.61  thf('64', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.44/0.61          | (m1_subset_1 @ (sk_D @ X8 @ X10 @ X9) @ (u1_struct_0 @ X9))
% 0.44/0.61          | (r1_lattice3 @ X9 @ X10 @ X8)
% 0.44/0.61          | ~ (l1_orders_2 @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.44/0.61  thf('65', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_orders_2 @ sk_B)
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.61  thf('66', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('67', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.44/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.44/0.61  thf('68', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.44/0.61  thf('69', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.61  thf('70', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('71', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.44/0.61          | ~ (r1_lattice3 @ X9 @ X10 @ X8)
% 0.44/0.61          | ~ (r2_hidden @ X11 @ X10)
% 0.44/0.61          | (r1_orders_2 @ X9 @ X8 @ X11)
% 0.44/0.61          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.44/0.61          | ~ (l1_orders_2 @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.44/0.61  thf('72', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (l1_orders_2 @ sk_A)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.44/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.44/0.61          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.44/0.61  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('74', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 0.44/0.61          | ~ (r2_hidden @ X0 @ X1)
% 0.44/0.61          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 0.44/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.44/0.61  thf('75', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 0.44/0.61          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_B) @ X1)
% 0.44/0.61          | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_B)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['69', '74'])).
% 0.44/0.61  thf('76', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_B))
% 0.44/0.61          | ~ (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X0 @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['62', '75'])).
% 0.44/0.61  thf('77', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 0.44/0.61          | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_B))
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X0 @ sk_D_2))),
% 0.44/0.61      inference('simplify', [status(thm)], ['76'])).
% 0.44/0.61  thf('78', plain,
% 0.44/0.61      ((((r1_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_B))))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['55', '77'])).
% 0.44/0.61  thf('79', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.61  thf('80', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(d9_orders_2, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( l1_orders_2 @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.61           ( ![C:$i]:
% 0.44/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.61               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.44/0.61                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf('81', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.44/0.61          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.44/0.61          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 0.44/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.44/0.61          | ~ (l1_orders_2 @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.44/0.61  thf('82', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (l1_orders_2 @ sk_A)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r2_hidden @ (k4_tarski @ sk_D_2 @ X0) @ (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['80', '81'])).
% 0.44/0.61  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('84', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r2_hidden @ (k4_tarski @ sk_D_2 @ X0) @ (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.44/0.61  thf('85', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_B))
% 0.44/0.61          | (r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_B)) @ 
% 0.44/0.61             (u1_orders_2 @ sk_A)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['79', '84'])).
% 0.44/0.61  thf('86', plain,
% 0.44/0.61      ((((r1_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | (r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_B)) @ 
% 0.44/0.61            (u1_orders_2 @ sk_A))
% 0.44/0.61         | (r1_lattice3 @ sk_B @ sk_C @ sk_D_2)))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['78', '85'])).
% 0.44/0.61  thf('87', plain,
% 0.44/0.61      ((((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_B)) @ 
% 0.44/0.61          (u1_orders_2 @ sk_A))
% 0.44/0.61         | (r1_lattice3 @ sk_B @ sk_C @ sk_D_2)))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['86'])).
% 0.44/0.61  thf('88', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_A))),
% 0.44/0.61      inference('eq_res', [status(thm)], ['15'])).
% 0.44/0.61  thf('89', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.44/0.61          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 0.44/0.61          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.44/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.44/0.61          | ~ (l1_orders_2 @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.44/0.61  thf('90', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (l1_orders_2 @ sk_B)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.44/0.61          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.44/0.61  thf('91', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('92', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.44/0.61          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.44/0.61      inference('demod', [status(thm)], ['90', '91'])).
% 0.44/0.61  thf('93', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.44/0.61  thf('94', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.44/0.61  thf('95', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.44/0.61  thf('96', plain,
% 0.44/0.61      ((((r1_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.44/0.61         | (r1_orders_2 @ sk_B @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_B))
% 0.44/0.61         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.44/0.61              (u1_struct_0 @ sk_A))))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['87', '95'])).
% 0.44/0.61  thf('97', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('98', plain,
% 0.44/0.61      ((((r1_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | (r1_orders_2 @ sk_B @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_B))
% 0.44/0.61         | ~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.44/0.61              (u1_struct_0 @ sk_A))))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('demod', [status(thm)], ['96', '97'])).
% 0.44/0.61  thf('99', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.61  thf('100', plain,
% 0.44/0.61      ((((r1_orders_2 @ sk_B @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_B))
% 0.44/0.61         | (r1_lattice3 @ sk_B @ sk_C @ sk_D_2)))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('clc', [status(thm)], ['98', '99'])).
% 0.44/0.61  thf('101', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.44/0.61  thf('102', plain,
% 0.44/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.44/0.61          | ~ (r1_orders_2 @ X9 @ X8 @ (sk_D @ X8 @ X10 @ X9))
% 0.44/0.61          | (r1_lattice3 @ X9 @ X10 @ X8)
% 0.44/0.61          | ~ (l1_orders_2 @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.44/0.61  thf('103', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | ~ (l1_orders_2 @ sk_B)
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (r1_orders_2 @ sk_B @ X0 @ (sk_D @ X0 @ X1 @ sk_B)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['101', '102'])).
% 0.44/0.61  thf('104', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('105', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_lattice3 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (r1_orders_2 @ sk_B @ X0 @ (sk_D @ X0 @ X1 @ sk_B)))),
% 0.44/0.61      inference('demod', [status(thm)], ['103', '104'])).
% 0.44/0.61  thf('106', plain,
% 0.44/0.61      ((((r1_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | (r1_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['100', '105'])).
% 0.44/0.61  thf('107', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('108', plain,
% 0.44/0.61      ((((r1_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | (r1_lattice3 @ sk_B @ sk_C @ sk_D_2)))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('demod', [status(thm)], ['106', '107'])).
% 0.44/0.61  thf('109', plain,
% 0.44/0.61      (((r1_lattice3 @ sk_B @ sk_C @ sk_D_2))
% 0.44/0.61         <= (((r1_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['108'])).
% 0.44/0.61  thf('110', plain,
% 0.44/0.61      ((~ (r1_lattice3 @ sk_B @ sk_C @ sk_E))
% 0.44/0.61         <= (~ ((r1_lattice3 @ sk_B @ sk_C @ sk_E)))),
% 0.44/0.61      inference('split', [status(esa)], ['48'])).
% 0.44/0.61  thf('111', plain, (((sk_D_2) = (sk_E))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('112', plain,
% 0.44/0.61      ((~ (r1_lattice3 @ sk_B @ sk_C @ sk_D_2))
% 0.44/0.61         <= (~ ((r1_lattice3 @ sk_B @ sk_C @ sk_E)))),
% 0.44/0.61      inference('demod', [status(thm)], ['110', '111'])).
% 0.44/0.61  thf('113', plain,
% 0.44/0.61      (((r1_lattice3 @ sk_B @ sk_C @ sk_E)) | 
% 0.44/0.61       ~ ((r1_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['109', '112'])).
% 0.44/0.61  thf('114', plain, (~ ((r2_lattice3 @ sk_B @ sk_C @ sk_E))),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['52', '54', '113'])).
% 0.44/0.61  thf('115', plain, (~ (r2_lattice3 @ sk_B @ sk_C @ sk_D_2)),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['51', '114'])).
% 0.44/0.61  thf('116', plain,
% 0.44/0.61      (((r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('clc', [status(thm)], ['47', '115'])).
% 0.44/0.61  thf('117', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['8', '27'])).
% 0.44/0.61  thf('118', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.44/0.61          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.44/0.61          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 0.44/0.61          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.44/0.61          | ~ (l1_orders_2 @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.44/0.61  thf('119', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ X1) @ 
% 0.44/0.61             (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['117', '118'])).
% 0.44/0.61  thf('120', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('121', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r2_lattice3 @ sk_B @ X0 @ sk_D_2)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ X1) @ 
% 0.44/0.61             (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_B) @ X1))),
% 0.44/0.61      inference('demod', [status(thm)], ['119', '120'])).
% 0.44/0.61  thf('122', plain,
% 0.44/0.61      ((((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2) @ 
% 0.44/0.61          (u1_orders_2 @ sk_A))
% 0.44/0.61         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))
% 0.44/0.61         | (r2_lattice3 @ sk_B @ sk_C @ sk_D_2)))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['116', '121'])).
% 0.44/0.61  thf('123', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('124', plain,
% 0.44/0.61      ((((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2) @ 
% 0.44/0.61          (u1_orders_2 @ sk_A))
% 0.44/0.61         | (r2_lattice3 @ sk_B @ sk_C @ sk_D_2)))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('demod', [status(thm)], ['122', '123'])).
% 0.44/0.61  thf('125', plain, (~ (r2_lattice3 @ sk_B @ sk_C @ sk_D_2)),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['51', '114'])).
% 0.44/0.61  thf('126', plain,
% 0.44/0.61      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2) @ 
% 0.44/0.61         (u1_orders_2 @ sk_A))) <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('clc', [status(thm)], ['124', '125'])).
% 0.44/0.61  thf('127', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.44/0.61  thf('128', plain,
% 0.44/0.61      (((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.44/0.61            (u1_struct_0 @ sk_A))
% 0.44/0.61         | (r1_orders_2 @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2)
% 0.44/0.61         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['126', '127'])).
% 0.44/0.61  thf('129', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('130', plain,
% 0.44/0.61      (((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.44/0.61            (u1_struct_0 @ sk_A))
% 0.44/0.61         | (r1_orders_2 @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2)))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('demod', [status(thm)], ['128', '129'])).
% 0.44/0.61  thf('131', plain,
% 0.44/0.61      ((((r2_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | (r1_orders_2 @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2)))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['28', '130'])).
% 0.44/0.61  thf('132', plain, (~ (r2_lattice3 @ sk_B @ sk_C @ sk_D_2)),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['51', '114'])).
% 0.44/0.61  thf('133', plain,
% 0.44/0.61      (((r1_orders_2 @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('clc', [status(thm)], ['131', '132'])).
% 0.44/0.61  thf('134', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('eq_res', [status(thm)], ['26'])).
% 0.44/0.61  thf('135', plain,
% 0.44/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.44/0.61          | ~ (r1_orders_2 @ X13 @ (sk_D_1 @ X12 @ X14 @ X13) @ X12)
% 0.44/0.61          | (r2_lattice3 @ X13 @ X14 @ X12)
% 0.44/0.61          | ~ (l1_orders_2 @ X13))),
% 0.44/0.61      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.44/0.61  thf('136', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | ~ (l1_orders_2 @ sk_B)
% 0.44/0.61          | (r2_lattice3 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (r1_orders_2 @ sk_B @ (sk_D_1 @ X0 @ X1 @ sk_B) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['134', '135'])).
% 0.44/0.61  thf('137', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('138', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.61          | (r2_lattice3 @ sk_B @ X1 @ X0)
% 0.44/0.61          | ~ (r1_orders_2 @ sk_B @ (sk_D_1 @ X0 @ X1 @ sk_B) @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['136', '137'])).
% 0.44/0.61  thf('139', plain,
% 0.44/0.61      ((((r2_lattice3 @ sk_B @ sk_C @ sk_D_2)
% 0.44/0.61         | ~ (m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['133', '138'])).
% 0.44/0.61  thf('140', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('141', plain,
% 0.44/0.61      (((r2_lattice3 @ sk_B @ sk_C @ sk_D_2))
% 0.44/0.61         <= (((r2_lattice3 @ sk_A @ sk_C @ sk_D_2)))),
% 0.44/0.61      inference('demod', [status(thm)], ['139', '140'])).
% 0.44/0.61  thf('142', plain, (~ (r2_lattice3 @ sk_B @ sk_C @ sk_D_2)),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['51', '114'])).
% 0.44/0.61  thf('143', plain, (~ ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['141', '142'])).
% 0.44/0.61  thf('144', plain,
% 0.44/0.61      (~ ((r1_lattice3 @ sk_B @ sk_C @ sk_E)) | 
% 0.44/0.61       ((r2_lattice3 @ sk_A @ sk_C @ sk_D_2))),
% 0.44/0.61      inference('split', [status(esa)], ['29'])).
% 0.44/0.61  thf('145', plain, ($false),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['1', '143', '144', '113'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
