%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PS5OTKwJBy

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:39 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  230 (9565 expanded)
%              Number of leaves         :   24 (2624 expanded)
%              Depth                    :   60
%              Number of atoms          : 2901 (135546 expanded)
%              Number of equality atoms :   40 (8987 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d12_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_lattice3 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_lattice3 @ A @ B @ D )
                 => ( r1_orders_2 @ A @ C @ D ) ) )
            & ( r2_lattice3 @ A @ B @ C )
            & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf(t3_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
              & ( v3_lattice3 @ A ) )
           => ( v3_lattice3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                  = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
                & ( v3_lattice3 @ A ) )
             => ( v3_lattice3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_yellow_0])).

thf('6',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
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

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_orders_2 @ X6 @ X7 )
       != ( g1_orders_2 @ X4 @ X5 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B_1 )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('15',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_orders_2 @ X6 @ X7 )
       != ( g1_orders_2 @ X4 @ X5 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B_1 )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('22',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B_1 )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

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

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ X1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ X1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_A ) @ X1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_A ) @ X1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ X14 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ sk_B_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ sk_B_1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ sk_A ) @ X1 @ sk_B_1 ) @ X1 )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ sk_A ) @ X1 @ sk_B_1 ) @ X1 )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_A ) @ X1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( r2_lattice3 @ X9 @ X10 @ ( sk_C @ X10 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_orders_2 @ X13 @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ X0 @ X3 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X3 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_orders_2 @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X2 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X2 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_A ) @ X1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ X2 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ X2 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X1 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_C @ X1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('86',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ X1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ X0 @ X1 @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v3_lattice3 @ sk_A )
      | ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','91'])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X8 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_lattice3 @ X9 @ ( sk_B @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( v3_lattice3 @ X9 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('97',plain,
    ( ~ ( l1_orders_2 @ sk_B_1 )
    | ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('101',plain,
    ( ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ~ ( v3_lattice3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','103'])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ X14 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('113',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('118',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('119',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('120',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_lattice3 @ X9 @ ( sk_B @ X9 ) @ ( sk_D @ X8 @ X9 ) )
      | ~ ( r2_lattice3 @ X9 @ ( sk_B @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( v3_lattice3 @ X9 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ( v3_lattice3 @ sk_B_1 )
      | ~ ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ X0 )
      | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_lattice3 @ sk_B_1 )
      | ~ ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ X0 )
      | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,(
    ~ ( v3_lattice3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['117','126'])).

thf('128',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('132',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('133',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_orders_2 @ X13 @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_lattice3 @ sk_B_1 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_lattice3 @ sk_B_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_orders_2 @ sk_B_1 @ X1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['130','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['116','139'])).

thf('141',plain,
    ( ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['111','140'])).

thf('142',plain,
    ( ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('144',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_B_1 ) )
      | ~ ( r1_orders_2 @ sk_B_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('149',plain,
    ( ( u1_orders_2 @ sk_B_1 )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_B_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_orders_2 @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','150'])).

thf('152',plain,
    ( ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) @ ( u1_orders_2 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('154',plain,
    ( ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) @ ( u1_orders_2 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) @ ( u1_orders_2 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('157',plain,
    ( ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('160',plain,
    ( ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('162',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['160','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('168',plain,(
    r2_lattice3 @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('170',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ~ ( r2_lattice3 @ X9 @ X10 @ X11 )
      | ( r1_orders_2 @ X9 @ ( sk_C @ X10 @ X9 ) @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( v3_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    r1_orders_2 @ sk_A @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['168','174'])).

thf('176',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_lattice3 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X10 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_orders_2 @ X0 @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_lattice3 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','179'])).

thf('181',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('184',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('186',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_B_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('188',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_B_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A )
    | ( r1_orders_2 @ sk_B_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','188'])).

thf('190',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    r1_orders_2 @ sk_B_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( sk_D @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_orders_2 @ X9 @ X8 @ ( sk_D @ X8 @ X9 ) )
      | ~ ( r2_lattice3 @ X9 @ ( sk_B @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( v3_lattice3 @ X9 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_lattice3])).

thf('194',plain,
    ( ~ ( l1_orders_2 @ sk_B_1 )
    | ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( r2_lattice3 @ sk_B_1 @ ( sk_B @ sk_B_1 ) @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('197',plain,(
    ! [X0: $i] :
      ( r2_lattice3 @ sk_B_1 @ X0 @ ( sk_C @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('198',plain,
    ( ( v3_lattice3 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    ~ ( v3_lattice3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ~ ( m1_subset_1 @ ( sk_C @ ( sk_B @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v3_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','200'])).

thf('202',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v3_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    $false ),
    inference(demod,[status(thm)],['201','202','203'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PS5OTKwJBy
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.04/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.28  % Solved by: fo/fo7.sh
% 1.04/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.28  % done 500 iterations in 0.828s
% 1.04/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.28  % SZS output start Refutation
% 1.04/1.28  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 1.04/1.28  thf(sk_B_type, type, sk_B: $i > $i).
% 1.04/1.28  thf(v3_lattice3_type, type, v3_lattice3: $i > $o).
% 1.04/1.28  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.04/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.04/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.28  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.04/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.28  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.04/1.28  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 1.04/1.28  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 1.04/1.28  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.04/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.04/1.28  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.04/1.28  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.04/1.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.04/1.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.04/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.28  thf(d12_lattice3, axiom,
% 1.04/1.28    (![A:$i]:
% 1.04/1.28     ( ( l1_orders_2 @ A ) =>
% 1.04/1.28       ( ( v3_lattice3 @ A ) <=>
% 1.04/1.28         ( ![B:$i]:
% 1.04/1.28           ( ?[C:$i]:
% 1.04/1.28             ( ( ![D:$i]:
% 1.04/1.28                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.28                   ( ( r2_lattice3 @ A @ B @ D ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) & 
% 1.04/1.28               ( r2_lattice3 @ A @ B @ C ) & 
% 1.04/1.28               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.04/1.28  thf('0', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('1', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('2', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('3', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('4', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('5', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf(t3_yellow_0, conjecture,
% 1.04/1.28    (![A:$i]:
% 1.04/1.28     ( ( l1_orders_2 @ A ) =>
% 1.04/1.28       ( ![B:$i]:
% 1.04/1.28         ( ( l1_orders_2 @ B ) =>
% 1.04/1.28           ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 1.04/1.28                 ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) & 
% 1.04/1.28               ( v3_lattice3 @ A ) ) =>
% 1.04/1.28             ( v3_lattice3 @ B ) ) ) ) ))).
% 1.04/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.28    (~( ![A:$i]:
% 1.04/1.28        ( ( l1_orders_2 @ A ) =>
% 1.04/1.28          ( ![B:$i]:
% 1.04/1.28            ( ( l1_orders_2 @ B ) =>
% 1.04/1.28              ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 1.04/1.28                    ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) & 
% 1.04/1.28                  ( v3_lattice3 @ A ) ) =>
% 1.04/1.28                ( v3_lattice3 @ B ) ) ) ) ) )),
% 1.04/1.28    inference('cnf.neg', [status(esa)], [t3_yellow_0])).
% 1.04/1.28  thf('6', plain,
% 1.04/1.28      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 1.04/1.28         = (g1_orders_2 @ (u1_struct_0 @ sk_B_1) @ (u1_orders_2 @ sk_B_1)))),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf(dt_u1_orders_2, axiom,
% 1.04/1.28    (![A:$i]:
% 1.04/1.28     ( ( l1_orders_2 @ A ) =>
% 1.04/1.28       ( m1_subset_1 @
% 1.04/1.28         ( u1_orders_2 @ A ) @ 
% 1.04/1.28         ( k1_zfmisc_1 @
% 1.04/1.28           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.04/1.28  thf('7', plain,
% 1.04/1.28      (![X3 : $i]:
% 1.04/1.28         ((m1_subset_1 @ (u1_orders_2 @ X3) @ 
% 1.04/1.28           (k1_zfmisc_1 @ 
% 1.04/1.28            (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X3))))
% 1.04/1.28          | ~ (l1_orders_2 @ X3))),
% 1.04/1.28      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 1.04/1.28  thf(free_g1_orders_2, axiom,
% 1.04/1.28    (![A:$i,B:$i]:
% 1.04/1.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 1.04/1.28       ( ![C:$i,D:$i]:
% 1.04/1.28         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 1.04/1.28           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.04/1.28  thf('8', plain,
% 1.04/1.28      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.04/1.28         (((g1_orders_2 @ X6 @ X7) != (g1_orders_2 @ X4 @ X5))
% 1.04/1.28          | ((X7) = (X5))
% 1.04/1.28          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X6))))),
% 1.04/1.28      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 1.04/1.28  thf('9', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ X0)
% 1.04/1.28          | ((u1_orders_2 @ X0) = (X1))
% 1.04/1.28          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 1.04/1.28              != (g1_orders_2 @ X2 @ X1)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['7', '8'])).
% 1.04/1.28  thf('10', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 1.04/1.28            != (g1_orders_2 @ X1 @ X0))
% 1.04/1.28          | ((u1_orders_2 @ sk_B_1) = (X0))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_B_1))),
% 1.04/1.28      inference('sup-', [status(thm)], ['6', '9'])).
% 1.04/1.28  thf('11', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('12', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 1.04/1.28            != (g1_orders_2 @ X1 @ X0))
% 1.04/1.28          | ((u1_orders_2 @ sk_B_1) = (X0)))),
% 1.04/1.28      inference('demod', [status(thm)], ['10', '11'])).
% 1.04/1.28  thf('13', plain, (((u1_orders_2 @ sk_B_1) = (u1_orders_2 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['12'])).
% 1.04/1.28  thf('14', plain,
% 1.04/1.28      (![X3 : $i]:
% 1.04/1.28         ((m1_subset_1 @ (u1_orders_2 @ X3) @ 
% 1.04/1.28           (k1_zfmisc_1 @ 
% 1.04/1.28            (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X3))))
% 1.04/1.28          | ~ (l1_orders_2 @ X3))),
% 1.04/1.28      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 1.04/1.28  thf('15', plain,
% 1.04/1.28      (((m1_subset_1 @ (u1_orders_2 @ sk_A) @ 
% 1.04/1.28         (k1_zfmisc_1 @ 
% 1.04/1.28          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))))
% 1.04/1.28        | ~ (l1_orders_2 @ sk_B_1))),
% 1.04/1.28      inference('sup+', [status(thm)], ['13', '14'])).
% 1.04/1.28  thf('16', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('17', plain,
% 1.04/1.28      ((m1_subset_1 @ (u1_orders_2 @ sk_A) @ 
% 1.04/1.28        (k1_zfmisc_1 @ 
% 1.04/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))))),
% 1.04/1.28      inference('demod', [status(thm)], ['15', '16'])).
% 1.04/1.28  thf('18', plain,
% 1.04/1.28      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.04/1.28         (((g1_orders_2 @ X6 @ X7) != (g1_orders_2 @ X4 @ X5))
% 1.04/1.28          | ((X6) = (X4))
% 1.04/1.28          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X6))))),
% 1.04/1.28      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 1.04/1.28  thf('19', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (((u1_struct_0 @ sk_B_1) = (X0))
% 1.04/1.28          | ((g1_orders_2 @ (u1_struct_0 @ sk_B_1) @ (u1_orders_2 @ sk_A))
% 1.04/1.28              != (g1_orders_2 @ X0 @ X1)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['17', '18'])).
% 1.04/1.28  thf('20', plain,
% 1.04/1.28      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 1.04/1.28         = (g1_orders_2 @ (u1_struct_0 @ sk_B_1) @ (u1_orders_2 @ sk_B_1)))),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('21', plain, (((u1_orders_2 @ sk_B_1) = (u1_orders_2 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['12'])).
% 1.04/1.28  thf('22', plain,
% 1.04/1.28      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 1.04/1.28         = (g1_orders_2 @ (u1_struct_0 @ sk_B_1) @ (u1_orders_2 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['20', '21'])).
% 1.04/1.28  thf('23', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (((u1_struct_0 @ sk_B_1) = (X0))
% 1.04/1.28          | ((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 1.04/1.28              != (g1_orders_2 @ X0 @ X1)))),
% 1.04/1.28      inference('demod', [status(thm)], ['19', '22'])).
% 1.04/1.28  thf('24', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf(d9_lattice3, axiom,
% 1.04/1.28    (![A:$i]:
% 1.04/1.28     ( ( l1_orders_2 @ A ) =>
% 1.04/1.28       ( ![B:$i,C:$i]:
% 1.04/1.28         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.28           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 1.04/1.28             ( ![D:$i]:
% 1.04/1.28               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.28                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 1.04/1.28  thf('25', plain,
% 1.04/1.28      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.28          | (m1_subset_1 @ (sk_D_1 @ X12 @ X14 @ X13) @ (u1_struct_0 @ X13))
% 1.04/1.28          | (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.28          | ~ (l1_orders_2 @ X13))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.28  thf('26', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_B_1)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | (m1_subset_1 @ (sk_D_1 @ X0 @ X1 @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['24', '25'])).
% 1.04/1.28  thf('27', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('28', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('29', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | (m1_subset_1 @ (sk_D_1 @ X0 @ X1 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.04/1.28  thf('30', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | ~ (v3_lattice3 @ sk_A)
% 1.04/1.28          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_A) @ X1 @ sk_B_1) @ 
% 1.04/1.28             (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['5', '29'])).
% 1.04/1.28  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('32', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('33', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_A) @ X1 @ sk_B_1) @ 
% 1.04/1.28           (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.04/1.28  thf('34', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('35', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('36', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('37', plain,
% 1.04/1.28      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.28          | (r2_hidden @ (sk_D_1 @ X12 @ X14 @ X13) @ X14)
% 1.04/1.28          | (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.28          | ~ (l1_orders_2 @ X13))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.28  thf('38', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_B_1)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ sk_B_1) @ X1))),
% 1.04/1.28      inference('sup-', [status(thm)], ['36', '37'])).
% 1.04/1.28  thf('39', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('40', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ sk_B_1) @ X1))),
% 1.04/1.28      inference('demod', [status(thm)], ['38', '39'])).
% 1.04/1.28  thf('41', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | ~ (v3_lattice3 @ sk_A)
% 1.04/1.28          | (r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ sk_A) @ X1 @ sk_B_1) @ X1)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['35', '40'])).
% 1.04/1.28  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('43', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('44', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ sk_A) @ X1 @ sk_B_1) @ X1)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.04/1.28  thf('45', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_A) @ X1 @ sk_B_1) @ 
% 1.04/1.28           (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.04/1.28  thf('46', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (r2_lattice3 @ X9 @ X10 @ (sk_C @ X10 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('47', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('48', plain,
% 1.04/1.28      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.28          | ~ (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.28          | ~ (r2_hidden @ X15 @ X14)
% 1.04/1.28          | (r1_orders_2 @ X13 @ X15 @ X12)
% 1.04/1.28          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 1.04/1.28          | ~ (l1_orders_2 @ X13))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.28  thf('49', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ X0)
% 1.04/1.28          | ~ (v3_lattice3 @ X0)
% 1.04/1.28          | ~ (l1_orders_2 @ X0)
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.04/1.28          | (r1_orders_2 @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 1.04/1.28          | ~ (r2_hidden @ X2 @ X3)
% 1.04/1.28          | ~ (r2_lattice3 @ X0 @ X3 @ (sk_C @ X1 @ X0)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['47', '48'])).
% 1.04/1.28  thf('50', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.28         (~ (r2_lattice3 @ X0 @ X3 @ (sk_C @ X1 @ X0))
% 1.04/1.28          | ~ (r2_hidden @ X2 @ X3)
% 1.04/1.28          | (r1_orders_2 @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.04/1.28          | ~ (v3_lattice3 @ X0)
% 1.04/1.28          | ~ (l1_orders_2 @ X0))),
% 1.04/1.28      inference('simplify', [status(thm)], ['49'])).
% 1.04/1.28  thf('51', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ X0)
% 1.04/1.28          | ~ (v3_lattice3 @ X0)
% 1.04/1.28          | ~ (l1_orders_2 @ X0)
% 1.04/1.28          | ~ (v3_lattice3 @ X0)
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.04/1.28          | (r1_orders_2 @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 1.04/1.28          | ~ (r2_hidden @ X2 @ X1))),
% 1.04/1.28      inference('sup-', [status(thm)], ['46', '50'])).
% 1.04/1.28  thf('52', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         (~ (r2_hidden @ X2 @ X1)
% 1.04/1.28          | (r1_orders_2 @ X0 @ X2 @ (sk_C @ X1 @ X0))
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.04/1.28          | ~ (v3_lattice3 @ X0)
% 1.04/1.28          | ~ (l1_orders_2 @ X0))),
% 1.04/1.28      inference('simplify', [status(thm)], ['51'])).
% 1.04/1.28  thf('53', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | ~ (v3_lattice3 @ sk_A)
% 1.04/1.28          | (r1_orders_2 @ sk_A @ 
% 1.04/1.28             (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X2 @ sk_A))
% 1.04/1.28          | ~ (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ X2))),
% 1.04/1.28      inference('sup-', [status(thm)], ['45', '52'])).
% 1.04/1.28  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('55', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('56', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | (r1_orders_2 @ sk_A @ 
% 1.04/1.28             (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X2 @ sk_A))
% 1.04/1.28          | ~ (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ X2))),
% 1.04/1.28      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.04/1.28  thf('57', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | (r1_orders_2 @ sk_A @ 
% 1.04/1.28             (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['44', '56'])).
% 1.04/1.28  thf('58', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r1_orders_2 @ sk_A @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ 
% 1.04/1.28           (sk_C @ X0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A)))),
% 1.04/1.28      inference('simplify', [status(thm)], ['57'])).
% 1.04/1.28  thf('59', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_A) @ X1 @ sk_B_1) @ 
% 1.04/1.28           (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.04/1.28  thf(d9_orders_2, axiom,
% 1.04/1.28    (![A:$i]:
% 1.04/1.28     ( ( l1_orders_2 @ A ) =>
% 1.04/1.28       ( ![B:$i]:
% 1.04/1.28         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.28           ( ![C:$i]:
% 1.04/1.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.28               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 1.04/1.28                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 1.04/1.28  thf('60', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.04/1.28          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 1.04/1.28          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.04/1.28          | ~ (l1_orders_2 @ X1))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_orders_2])).
% 1.04/1.28  thf('61', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ X2) @ 
% 1.04/1.28             (u1_orders_2 @ sk_A))
% 1.04/1.28          | ~ (r1_orders_2 @ sk_A @ 
% 1.04/1.28               (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ X2))),
% 1.04/1.28      inference('sup-', [status(thm)], ['59', '60'])).
% 1.04/1.28  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('63', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ X2) @ 
% 1.04/1.28             (u1_orders_2 @ sk_A))
% 1.04/1.28          | ~ (r1_orders_2 @ sk_A @ 
% 1.04/1.28               (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ X2))),
% 1.04/1.28      inference('demod', [status(thm)], ['61', '62'])).
% 1.04/1.28  thf('64', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ 
% 1.04/1.28              (sk_C @ X0 @ sk_A)) @ 
% 1.04/1.28             (u1_orders_2 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['58', '63'])).
% 1.04/1.28  thf('65', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ 
% 1.04/1.28              (sk_C @ X0 @ sk_A)) @ 
% 1.04/1.28             (u1_orders_2 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A)))),
% 1.04/1.28      inference('simplify', [status(thm)], ['64'])).
% 1.04/1.28  thf('66', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | ~ (v3_lattice3 @ sk_A)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ 
% 1.04/1.28              (sk_C @ X0 @ sk_A)) @ 
% 1.04/1.28             (u1_orders_2 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['34', '65'])).
% 1.04/1.28  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('68', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('69', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ 
% 1.04/1.28              (sk_C @ X0 @ sk_A)) @ 
% 1.04/1.28             (u1_orders_2 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.04/1.28  thf('70', plain, (((u1_orders_2 @ sk_B_1) = (u1_orders_2 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['12'])).
% 1.04/1.28  thf('71', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.04/1.28          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 1.04/1.28          | (r1_orders_2 @ X1 @ X0 @ X2)
% 1.04/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.04/1.28          | ~ (l1_orders_2 @ X1))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_orders_2])).
% 1.04/1.28  thf('72', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_B_1)
% 1.04/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 1.04/1.28          | (r1_orders_2 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['70', '71'])).
% 1.04/1.28  thf('73', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('74', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 1.04/1.28          | (r1_orders_2 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1)))),
% 1.04/1.28      inference('demod', [status(thm)], ['72', '73'])).
% 1.04/1.28  thf('75', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('76', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('77', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r1_orders_2 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.04/1.28  thf('78', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ 
% 1.04/1.28               (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r1_orders_2 @ sk_B_1 @ 
% 1.04/1.28             (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X0 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['69', '77'])).
% 1.04/1.28  thf('79', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r1_orders_2 @ sk_B_1 @ 
% 1.04/1.28             (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['33', '78'])).
% 1.04/1.28  thf('80', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r1_orders_2 @ sk_B_1 @ 
% 1.04/1.28           (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X0 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A)))),
% 1.04/1.28      inference('simplify', [status(thm)], ['79'])).
% 1.04/1.28  thf('81', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | ~ (v3_lattice3 @ sk_A)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | (r1_orders_2 @ sk_B_1 @ 
% 1.04/1.28             (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['4', '80'])).
% 1.04/1.28  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('83', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('84', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X1 @ sk_A))
% 1.04/1.28          | (r1_orders_2 @ sk_B_1 @ 
% 1.04/1.28             (sk_D_1 @ (sk_C @ X1 @ sk_A) @ X0 @ sk_B_1) @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.04/1.28  thf('85', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('86', plain,
% 1.04/1.28      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.28          | ~ (r1_orders_2 @ X13 @ (sk_D_1 @ X12 @ X14 @ X13) @ X12)
% 1.04/1.28          | (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.28          | ~ (l1_orders_2 @ X13))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.28  thf('87', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_B_1)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | ~ (r1_orders_2 @ sk_B_1 @ (sk_D_1 @ X0 @ X1 @ sk_B_1) @ X0))),
% 1.04/1.28      inference('sup-', [status(thm)], ['85', '86'])).
% 1.04/1.28  thf('88', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('89', plain,
% 1.04/1.28      (![X0 : $i, X1 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X1 @ X0)
% 1.04/1.28          | ~ (r1_orders_2 @ sk_B_1 @ (sk_D_1 @ X0 @ X1 @ sk_B_1) @ X0))),
% 1.04/1.28      inference('demod', [status(thm)], ['87', '88'])).
% 1.04/1.28  thf('90', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X0 @ sk_A))
% 1.04/1.28          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['84', '89'])).
% 1.04/1.28  thf('91', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('simplify', [status(thm)], ['90'])).
% 1.04/1.28  thf('92', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | ~ (v3_lattice3 @ sk_A)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['3', '91'])).
% 1.04/1.28  thf('93', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('94', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('95', plain,
% 1.04/1.28      (![X0 : $i]: (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X0 @ sk_A))),
% 1.04/1.28      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.04/1.28  thf('96', plain,
% 1.04/1.28      (![X8 : $i, X9 : $i]:
% 1.04/1.28         ((m1_subset_1 @ (sk_D @ X8 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (r2_lattice3 @ X9 @ (sk_B @ X9) @ X8)
% 1.04/1.28          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 1.04/1.28          | (v3_lattice3 @ X9)
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('97', plain,
% 1.04/1.28      ((~ (l1_orders_2 @ sk_B_1)
% 1.04/1.28        | (v3_lattice3 @ sk_B_1)
% 1.04/1.28        | ~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.28             (u1_struct_0 @ sk_B_1))
% 1.04/1.28        | (m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28           (u1_struct_0 @ sk_B_1)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['95', '96'])).
% 1.04/1.28  thf('98', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('99', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('100', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('101', plain,
% 1.04/1.28      (((v3_lattice3 @ sk_B_1)
% 1.04/1.28        | ~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.28             (u1_struct_0 @ sk_A))
% 1.04/1.28        | (m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28           (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 1.04/1.28  thf('102', plain, (~ (v3_lattice3 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('103', plain,
% 1.04/1.28      (((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28         (u1_struct_0 @ sk_A))
% 1.04/1.28        | ~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.28             (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('clc', [status(thm)], ['101', '102'])).
% 1.04/1.28  thf('104', plain,
% 1.04/1.28      ((~ (l1_orders_2 @ sk_A)
% 1.04/1.28        | ~ (v3_lattice3 @ sk_A)
% 1.04/1.28        | (m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28           (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['2', '103'])).
% 1.04/1.28  thf('105', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('106', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('107', plain,
% 1.04/1.28      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28        (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.28  thf('108', plain,
% 1.04/1.28      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.28          | (r2_hidden @ (sk_D_1 @ X12 @ X14 @ X13) @ X14)
% 1.04/1.28          | (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.28          | ~ (l1_orders_2 @ X13))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.28  thf('109', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | (r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.28             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28              X0 @ sk_A) @ 
% 1.04/1.28             X0))),
% 1.04/1.28      inference('sup-', [status(thm)], ['107', '108'])).
% 1.04/1.28  thf('110', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('111', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.28           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.28          | (r2_hidden @ 
% 1.04/1.28             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28              X0 @ sk_A) @ 
% 1.04/1.28             X0))),
% 1.04/1.28      inference('demod', [status(thm)], ['109', '110'])).
% 1.04/1.28  thf('112', plain,
% 1.04/1.28      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28        (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.28  thf('113', plain,
% 1.04/1.28      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.28          | (m1_subset_1 @ (sk_D_1 @ X12 @ X14 @ X13) @ (u1_struct_0 @ X13))
% 1.04/1.28          | (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.28          | ~ (l1_orders_2 @ X13))),
% 1.04/1.28      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.28  thf('114', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         (~ (l1_orders_2 @ sk_A)
% 1.04/1.28          | (r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.28             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.28          | (m1_subset_1 @ 
% 1.04/1.28             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28              X0 @ sk_A) @ 
% 1.04/1.28             (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['112', '113'])).
% 1.04/1.28  thf('115', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('116', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         ((r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.28           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.28          | (m1_subset_1 @ 
% 1.04/1.28             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.28              X0 @ sk_A) @ 
% 1.04/1.28             (u1_struct_0 @ sk_A)))),
% 1.04/1.28      inference('demod', [status(thm)], ['114', '115'])).
% 1.04/1.28  thf('117', plain,
% 1.04/1.28      (![X9 : $i, X10 : $i]:
% 1.04/1.28         (~ (v3_lattice3 @ X9)
% 1.04/1.28          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('118', plain,
% 1.04/1.28      (![X0 : $i]: (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X0 @ sk_A))),
% 1.04/1.28      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.04/1.28  thf('119', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.28      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.28  thf('120', plain,
% 1.04/1.28      (![X8 : $i, X9 : $i]:
% 1.04/1.28         ((r2_lattice3 @ X9 @ (sk_B @ X9) @ (sk_D @ X8 @ X9))
% 1.04/1.28          | ~ (r2_lattice3 @ X9 @ (sk_B @ X9) @ X8)
% 1.04/1.28          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 1.04/1.28          | (v3_lattice3 @ X9)
% 1.04/1.28          | ~ (l1_orders_2 @ X9))),
% 1.04/1.28      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.28  thf('121', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | ~ (l1_orders_2 @ sk_B_1)
% 1.04/1.28          | (v3_lattice3 @ sk_B_1)
% 1.04/1.28          | ~ (r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ X0)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ (sk_D @ X0 @ sk_B_1)))),
% 1.04/1.28      inference('sup-', [status(thm)], ['119', '120'])).
% 1.04/1.28  thf('122', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.28  thf('123', plain,
% 1.04/1.28      (![X0 : $i]:
% 1.04/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.28          | (v3_lattice3 @ sk_B_1)
% 1.04/1.28          | ~ (r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ X0)
% 1.04/1.28          | (r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ (sk_D @ X0 @ sk_B_1)))),
% 1.04/1.28      inference('demod', [status(thm)], ['121', '122'])).
% 1.04/1.28  thf('124', plain,
% 1.04/1.28      (((r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ 
% 1.04/1.28         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | (v3_lattice3 @ sk_B_1)
% 1.04/1.29        | ~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['118', '123'])).
% 1.04/1.29  thf('125', plain, (~ (v3_lattice3 @ sk_B_1)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('126', plain,
% 1.04/1.29      ((~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.29        | (r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('clc', [status(thm)], ['124', '125'])).
% 1.04/1.29  thf('127', plain,
% 1.04/1.29      ((~ (l1_orders_2 @ sk_A)
% 1.04/1.29        | ~ (v3_lattice3 @ sk_A)
% 1.04/1.29        | (r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['117', '126'])).
% 1.04/1.29  thf('128', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('129', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('130', plain,
% 1.04/1.29      ((r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ 
% 1.04/1.29        (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))),
% 1.04/1.29      inference('demod', [status(thm)], ['127', '128', '129'])).
% 1.04/1.29  thf('131', plain,
% 1.04/1.29      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29        (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.29  thf('132', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.29  thf('133', plain,
% 1.04/1.29      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.29          | ~ (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.29          | ~ (r2_hidden @ X15 @ X14)
% 1.04/1.29          | (r1_orders_2 @ X13 @ X15 @ X12)
% 1.04/1.29          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 1.04/1.29          | ~ (l1_orders_2 @ X13))),
% 1.04/1.29      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.29  thf('134', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | ~ (l1_orders_2 @ sk_B_1)
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 1.04/1.29          | (r1_orders_2 @ sk_B_1 @ X1 @ X0)
% 1.04/1.29          | ~ (r2_hidden @ X1 @ X2)
% 1.04/1.29          | ~ (r2_lattice3 @ sk_B_1 @ X2 @ X0))),
% 1.04/1.29      inference('sup-', [status(thm)], ['132', '133'])).
% 1.04/1.29  thf('135', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('136', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.29  thf('137', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | (r1_orders_2 @ sk_B_1 @ X1 @ X0)
% 1.04/1.29          | ~ (r2_hidden @ X1 @ X2)
% 1.04/1.29          | ~ (r2_lattice3 @ sk_B_1 @ X2 @ X0))),
% 1.04/1.29      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.04/1.29  thf('138', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (r2_lattice3 @ sk_B_1 @ X0 @ 
% 1.04/1.29             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r2_hidden @ X1 @ X0)
% 1.04/1.29          | (r1_orders_2 @ sk_B_1 @ X1 @ 
% 1.04/1.29             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['131', '137'])).
% 1.04/1.29  thf('139', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | (r1_orders_2 @ sk_B_1 @ X0 @ 
% 1.04/1.29             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r2_hidden @ X0 @ (sk_B @ sk_B_1)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['130', '138'])).
% 1.04/1.29  thf('140', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         ((r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r2_hidden @ 
% 1.04/1.29               (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29                X0 @ sk_A) @ 
% 1.04/1.29               (sk_B @ sk_B_1))
% 1.04/1.29          | (r1_orders_2 @ sk_B_1 @ 
% 1.04/1.29             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29              X0 @ sk_A) @ 
% 1.04/1.29             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['116', '139'])).
% 1.04/1.29  thf('141', plain,
% 1.04/1.29      (((r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | (r1_orders_2 @ sk_B_1 @ 
% 1.04/1.29           (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29            (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | (r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['111', '140'])).
% 1.04/1.29  thf('142', plain,
% 1.04/1.29      (((r1_orders_2 @ sk_B_1 @ 
% 1.04/1.29         (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29          (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | (r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('simplify', [status(thm)], ['141'])).
% 1.04/1.29  thf('143', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         ((r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | (m1_subset_1 @ 
% 1.04/1.29             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29              X0 @ sk_A) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('demod', [status(thm)], ['114', '115'])).
% 1.04/1.29  thf('144', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.29  thf('145', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.04/1.29          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 1.04/1.29          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 1.04/1.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.04/1.29          | ~ (l1_orders_2 @ X1))),
% 1.04/1.29      inference('cnf', [status(esa)], [d9_orders_2])).
% 1.04/1.29  thf('146', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | ~ (l1_orders_2 @ sk_B_1)
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 1.04/1.29          | (r2_hidden @ (k4_tarski @ X0 @ X1) @ (u1_orders_2 @ sk_B_1))
% 1.04/1.29          | ~ (r1_orders_2 @ sk_B_1 @ X0 @ X1))),
% 1.04/1.29      inference('sup-', [status(thm)], ['144', '145'])).
% 1.04/1.29  thf('147', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('148', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.29  thf('149', plain, (((u1_orders_2 @ sk_B_1) = (u1_orders_2 @ sk_A))),
% 1.04/1.29      inference('eq_res', [status(thm)], ['12'])).
% 1.04/1.29  thf('150', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | (r2_hidden @ (k4_tarski @ X0 @ X1) @ (u1_orders_2 @ sk_A))
% 1.04/1.29          | ~ (r1_orders_2 @ sk_B_1 @ X0 @ X1))),
% 1.04/1.29      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 1.04/1.29  thf('151', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         ((r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r1_orders_2 @ sk_B_1 @ 
% 1.04/1.29               (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29                X0 @ sk_A) @ 
% 1.04/1.29               X1)
% 1.04/1.29          | (r2_hidden @ 
% 1.04/1.29             (k4_tarski @ 
% 1.04/1.29              (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29               X0 @ sk_A) @ 
% 1.04/1.29              X1) @ 
% 1.04/1.29             (u1_orders_2 @ sk_A))
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['143', '150'])).
% 1.04/1.29  thf('152', plain,
% 1.04/1.29      (((r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | ~ (m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A))
% 1.04/1.29        | (r2_hidden @ 
% 1.04/1.29           (k4_tarski @ 
% 1.04/1.29            (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29             (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29            (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)) @ 
% 1.04/1.29           (u1_orders_2 @ sk_A))
% 1.04/1.29        | (r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['142', '151'])).
% 1.04/1.29  thf('153', plain,
% 1.04/1.29      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29        (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.29  thf('154', plain,
% 1.04/1.29      (((r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | (r2_hidden @ 
% 1.04/1.29           (k4_tarski @ 
% 1.04/1.29            (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29             (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29            (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)) @ 
% 1.04/1.29           (u1_orders_2 @ sk_A))
% 1.04/1.29        | (r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('demod', [status(thm)], ['152', '153'])).
% 1.04/1.29  thf('155', plain,
% 1.04/1.29      (((r2_hidden @ 
% 1.04/1.29         (k4_tarski @ 
% 1.04/1.29          (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29           (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29          (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)) @ 
% 1.04/1.29         (u1_orders_2 @ sk_A))
% 1.04/1.29        | (r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('simplify', [status(thm)], ['154'])).
% 1.04/1.29  thf('156', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.04/1.29          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 1.04/1.29          | (r1_orders_2 @ X1 @ X0 @ X2)
% 1.04/1.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.04/1.29          | ~ (l1_orders_2 @ X1))),
% 1.04/1.29      inference('cnf', [status(esa)], [d9_orders_2])).
% 1.04/1.29  thf('157', plain,
% 1.04/1.29      (((r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | ~ (l1_orders_2 @ sk_A)
% 1.04/1.29        | ~ (m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A))
% 1.04/1.29        | (r1_orders_2 @ sk_A @ 
% 1.04/1.29           (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29            (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | ~ (m1_subset_1 @ 
% 1.04/1.29             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29              (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['155', '156'])).
% 1.04/1.29  thf('158', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('159', plain,
% 1.04/1.29      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29        (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.29  thf('160', plain,
% 1.04/1.29      (((r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | (r1_orders_2 @ sk_A @ 
% 1.04/1.29           (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29            (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | ~ (m1_subset_1 @ 
% 1.04/1.29             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29              (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('demod', [status(thm)], ['157', '158', '159'])).
% 1.04/1.29  thf('161', plain,
% 1.04/1.29      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29        (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.29  thf('162', plain,
% 1.04/1.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 1.04/1.29          | ~ (r1_orders_2 @ X13 @ (sk_D_1 @ X12 @ X14 @ X13) @ X12)
% 1.04/1.29          | (r2_lattice3 @ X13 @ X14 @ X12)
% 1.04/1.29          | ~ (l1_orders_2 @ X13))),
% 1.04/1.29      inference('cnf', [status(esa)], [d9_lattice3])).
% 1.04/1.29  thf('163', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (l1_orders_2 @ sk_A)
% 1.04/1.29          | (r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r1_orders_2 @ sk_A @ 
% 1.04/1.29               (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29                X0 @ sk_A) @ 
% 1.04/1.29               (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['161', '162'])).
% 1.04/1.29  thf('164', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('165', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         ((r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r1_orders_2 @ sk_A @ 
% 1.04/1.29               (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29                X0 @ sk_A) @ 
% 1.04/1.29               (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('demod', [status(thm)], ['163', '164'])).
% 1.04/1.29  thf('166', plain,
% 1.04/1.29      ((~ (m1_subset_1 @ 
% 1.04/1.29           (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29            (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29           (u1_struct_0 @ sk_A))
% 1.04/1.29        | (r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('clc', [status(thm)], ['160', '165'])).
% 1.04/1.29  thf('167', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         ((r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | (m1_subset_1 @ 
% 1.04/1.29             (sk_D_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29              X0 @ sk_A) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('demod', [status(thm)], ['114', '115'])).
% 1.04/1.29  thf('168', plain,
% 1.04/1.29      ((r2_lattice3 @ sk_A @ (sk_B @ sk_B_1) @ 
% 1.04/1.29        (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))),
% 1.04/1.29      inference('clc', [status(thm)], ['166', '167'])).
% 1.04/1.29  thf('169', plain,
% 1.04/1.29      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29        (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.29  thf('170', plain,
% 1.04/1.29      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.29         (~ (v3_lattice3 @ X9)
% 1.04/1.29          | ~ (r2_lattice3 @ X9 @ X10 @ X11)
% 1.04/1.29          | (r1_orders_2 @ X9 @ (sk_C @ X10 @ X9) @ X11)
% 1.04/1.29          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 1.04/1.29          | ~ (l1_orders_2 @ X9))),
% 1.04/1.29      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.29  thf('171', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         (~ (l1_orders_2 @ sk_A)
% 1.04/1.29          | (r1_orders_2 @ sk_A @ (sk_C @ X0 @ sk_A) @ 
% 1.04/1.29             (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29               (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (v3_lattice3 @ sk_A))),
% 1.04/1.29      inference('sup-', [status(thm)], ['169', '170'])).
% 1.04/1.29  thf('172', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('173', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('174', plain,
% 1.04/1.29      (![X0 : $i]:
% 1.04/1.29         ((r1_orders_2 @ sk_A @ (sk_C @ X0 @ sk_A) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 1.04/1.29               (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('demod', [status(thm)], ['171', '172', '173'])).
% 1.04/1.29  thf('175', plain,
% 1.04/1.29      ((r1_orders_2 @ sk_A @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29        (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))),
% 1.04/1.29      inference('sup-', [status(thm)], ['168', '174'])).
% 1.04/1.29  thf('176', plain,
% 1.04/1.29      (![X9 : $i, X10 : $i]:
% 1.04/1.29         (~ (v3_lattice3 @ X9)
% 1.04/1.29          | (m1_subset_1 @ (sk_C @ X10 @ X9) @ (u1_struct_0 @ X9))
% 1.04/1.29          | ~ (l1_orders_2 @ X9))),
% 1.04/1.29      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.29  thf('177', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.04/1.29          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 1.04/1.29          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 1.04/1.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.04/1.29          | ~ (l1_orders_2 @ X1))),
% 1.04/1.29      inference('cnf', [status(esa)], [d9_orders_2])).
% 1.04/1.29  thf('178', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (~ (l1_orders_2 @ X0)
% 1.04/1.29          | ~ (v3_lattice3 @ X0)
% 1.04/1.29          | ~ (l1_orders_2 @ X0)
% 1.04/1.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.04/1.29          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ X2) @ 
% 1.04/1.29             (u1_orders_2 @ X0))
% 1.04/1.29          | ~ (r1_orders_2 @ X0 @ (sk_C @ X1 @ X0) @ X2))),
% 1.04/1.29      inference('sup-', [status(thm)], ['176', '177'])).
% 1.04/1.29  thf('179', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.29         (~ (r1_orders_2 @ X0 @ (sk_C @ X1 @ X0) @ X2)
% 1.04/1.29          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ X2) @ 
% 1.04/1.29             (u1_orders_2 @ X0))
% 1.04/1.29          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.04/1.29          | ~ (v3_lattice3 @ X0)
% 1.04/1.29          | ~ (l1_orders_2 @ X0))),
% 1.04/1.29      inference('simplify', [status(thm)], ['178'])).
% 1.04/1.29  thf('180', plain,
% 1.04/1.29      ((~ (l1_orders_2 @ sk_A)
% 1.04/1.29        | ~ (v3_lattice3 @ sk_A)
% 1.04/1.29        | ~ (m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A))
% 1.04/1.29        | (r2_hidden @ 
% 1.04/1.29           (k4_tarski @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29            (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)) @ 
% 1.04/1.29           (u1_orders_2 @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['175', '179'])).
% 1.04/1.29  thf('181', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('182', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('183', plain,
% 1.04/1.29      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29        (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.29  thf('184', plain,
% 1.04/1.29      ((r2_hidden @ 
% 1.04/1.29        (k4_tarski @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29         (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)) @ 
% 1.04/1.29        (u1_orders_2 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 1.04/1.29  thf('185', plain,
% 1.04/1.29      (![X0 : $i, X1 : $i]:
% 1.04/1.29         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 1.04/1.29          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.29          | (r1_orders_2 @ sk_B_1 @ X1 @ X0)
% 1.04/1.29          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.04/1.29  thf('186', plain,
% 1.04/1.29      ((~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.29        | (r1_orders_2 @ sk_B_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))
% 1.04/1.29        | ~ (m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['184', '185'])).
% 1.04/1.29  thf('187', plain,
% 1.04/1.29      ((m1_subset_1 @ (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1) @ 
% 1.04/1.29        (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.04/1.29  thf('188', plain,
% 1.04/1.29      ((~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.04/1.29        | (r1_orders_2 @ sk_B_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('demod', [status(thm)], ['186', '187'])).
% 1.04/1.29  thf('189', plain,
% 1.04/1.29      ((~ (l1_orders_2 @ sk_A)
% 1.04/1.29        | ~ (v3_lattice3 @ sk_A)
% 1.04/1.29        | (r1_orders_2 @ sk_B_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29           (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['1', '188'])).
% 1.04/1.29  thf('190', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('191', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('192', plain,
% 1.04/1.29      ((r1_orders_2 @ sk_B_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29        (sk_D @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ sk_B_1))),
% 1.04/1.29      inference('demod', [status(thm)], ['189', '190', '191'])).
% 1.04/1.29  thf('193', plain,
% 1.04/1.29      (![X8 : $i, X9 : $i]:
% 1.04/1.29         (~ (r1_orders_2 @ X9 @ X8 @ (sk_D @ X8 @ X9))
% 1.04/1.29          | ~ (r2_lattice3 @ X9 @ (sk_B @ X9) @ X8)
% 1.04/1.29          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 1.04/1.29          | (v3_lattice3 @ X9)
% 1.04/1.29          | ~ (l1_orders_2 @ X9))),
% 1.04/1.29      inference('cnf', [status(esa)], [d12_lattice3])).
% 1.04/1.29  thf('194', plain,
% 1.04/1.29      ((~ (l1_orders_2 @ sk_B_1)
% 1.04/1.29        | (v3_lattice3 @ sk_B_1)
% 1.04/1.29        | ~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29             (u1_struct_0 @ sk_B_1))
% 1.04/1.29        | ~ (r2_lattice3 @ sk_B_1 @ (sk_B @ sk_B_1) @ 
% 1.04/1.29             (sk_C @ (sk_B @ sk_B_1) @ sk_A)))),
% 1.04/1.29      inference('sup-', [status(thm)], ['192', '193'])).
% 1.04/1.29  thf('195', plain, ((l1_orders_2 @ sk_B_1)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('196', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('eq_res', [status(thm)], ['23'])).
% 1.04/1.29  thf('197', plain,
% 1.04/1.29      (![X0 : $i]: (r2_lattice3 @ sk_B_1 @ X0 @ (sk_C @ X0 @ sk_A))),
% 1.04/1.29      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.04/1.29  thf('198', plain,
% 1.04/1.29      (((v3_lattice3 @ sk_B_1)
% 1.04/1.29        | ~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ 
% 1.04/1.29             (u1_struct_0 @ sk_A)))),
% 1.04/1.29      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 1.04/1.29  thf('199', plain, (~ (v3_lattice3 @ sk_B_1)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('200', plain,
% 1.04/1.29      (~ (m1_subset_1 @ (sk_C @ (sk_B @ sk_B_1) @ sk_A) @ (u1_struct_0 @ sk_A))),
% 1.04/1.29      inference('clc', [status(thm)], ['198', '199'])).
% 1.04/1.29  thf('201', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v3_lattice3 @ sk_A))),
% 1.04/1.29      inference('sup-', [status(thm)], ['0', '200'])).
% 1.04/1.29  thf('202', plain, ((l1_orders_2 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('203', plain, ((v3_lattice3 @ sk_A)),
% 1.04/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.29  thf('204', plain, ($false),
% 1.04/1.29      inference('demod', [status(thm)], ['201', '202', '203'])).
% 1.04/1.29  
% 1.04/1.29  % SZS output end Refutation
% 1.04/1.29  
% 1.04/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
