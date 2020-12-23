%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1571+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YsFI2xzp37

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 729 expanded)
%              Number of leaves         :   17 ( 197 expanded)
%              Depth                    :   32
%              Number of atoms          : 1254 (12413 expanded)
%              Number of equality atoms :   21 ( 300 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(t49_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ( r2_yellow_0 @ A @ B )
            & ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r1_lattice3 @ A @ B @ D )
                <=> ( r1_lattice3 @ A @ C @ D ) ) ) )
         => ( ( k2_yellow_0 @ A @ B )
            = ( k2_yellow_0 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( ( r2_yellow_0 @ A @ B )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_lattice3 @ A @ B @ D )
                  <=> ( r1_lattice3 @ A @ C @ D ) ) ) )
           => ( ( k2_yellow_0 @ A @ B )
              = ( k2_yellow_0 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_yellow_0])).

thf('1',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r1_lattice3 @ A @ B @ D )
                <=> ( r1_lattice3 @ A @ C @ D ) ) )
            & ( r2_yellow_0 @ A @ B ) )
         => ( r2_yellow_0 @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_yellow_0 @ X6 @ X7 )
      | ( r1_lattice3 @ X6 @ X8 @ ( sk_D_1 @ X7 @ X8 @ X6 ) )
      | ( r1_lattice3 @ X6 @ X7 @ ( sk_D_1 @ X7 @ X8 @ X6 ) )
      | ~ ( r2_yellow_0 @ X6 @ X8 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_yellow_0 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_D_1 @ X7 @ X8 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_yellow_0 @ X6 @ X8 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ sk_B @ X9 )
      | ( r1_lattice3 @ sk_A @ sk_C @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_A @ X0 )
      | ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_A @ X0 )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X9: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ sk_C @ X9 )
      | ( r1_lattice3 @ sk_A @ sk_B @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_A @ X0 )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_C )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_yellow_0 @ X6 @ X7 )
      | ~ ( r1_lattice3 @ X6 @ X8 @ ( sk_D_1 @ X7 @ X8 @ X6 ) )
      | ~ ( r1_lattice3 @ X6 @ X7 @ ( sk_D_1 @ X7 @ X8 @ X6 ) )
      | ~ ( r2_yellow_0 @ X6 @ X8 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_yellow_0])).

thf('26',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('32',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_yellow_0 @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf(d10_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_yellow_0 @ A @ B )
           => ( ( C
                = ( k2_yellow_0 @ A @ B ) )
            <=> ( ( r1_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('44',plain,(
    ! [X9: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ sk_C @ X9 )
      | ( r1_lattice3 @ sk_A @ sk_B @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_lattice3 @ sk_A @ sk_C @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( X2
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X2 )
      | ( ( k2_yellow_0 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_yellow_0 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X9: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ sk_B @ X9 )
      | ( r1_lattice3 @ sk_A @ sk_C @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_lattice3 @ X0 @ X1 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( X2
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X2 )
      | ( ( k2_yellow_0 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ X2 ) )
      | ( r1_lattice3 @ X0 @ X2 @ ( sk_D @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) )
      | ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ( r1_lattice3 @ X0 @ X2 @ ( sk_D @ ( k2_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) )
      | ( ( k2_yellow_0 @ X0 @ X1 )
        = ( k2_yellow_0 @ X0 @ X2 ) )
      | ~ ( r2_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ( r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_lattice3 @ sk_A @ sk_B @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_lattice3 @ sk_A @ sk_C @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','71'])).

thf('73',plain,(
    m1_subset_1 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
       != ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X3 )
      | ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ ( k2_yellow_0 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X3 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X3 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ X2 @ ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r2_yellow_0 @ sk_A @ sk_C )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','81'])).

thf('83',plain,(
    r2_yellow_0 @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['32','33'])).

thf('84',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ ( k2_yellow_0 @ sk_A @ sk_C ) @ sk_B @ sk_A ) @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_yellow_0])).

thf('86',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( r2_yellow_0 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_A @ sk_B ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r2_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r1_lattice3 @ sk_A @ sk_B @ ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_yellow_0 @ sk_A @ sk_C )
      = ( k2_yellow_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ( k2_yellow_0 @ sk_A @ sk_B )
 != ( k2_yellow_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ~ ( m1_subset_1 @ ( k2_yellow_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','92'])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['93','94'])).


%------------------------------------------------------------------------------
