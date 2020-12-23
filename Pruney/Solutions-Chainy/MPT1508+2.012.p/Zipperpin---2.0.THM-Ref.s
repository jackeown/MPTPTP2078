%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LktrquxRRd

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:32 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 277 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   22
%              Number of atoms          : 1315 (4320 expanded)
%              Number of equality atoms :   43 ( 167 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(t42_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r3_lattice3 @ A @ B @ C ) )
             => ( ( k16_lattice3 @ A @ C )
                = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ( r2_hidden @ B @ C )
                  & ( r3_lattice3 @ A @ B @ C ) )
               => ( ( k16_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( B
                = ( k16_lattice3 @ A @ C ) )
            <=> ( ( r3_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r3_lattice3 @ A @ D @ C )
                     => ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_lattice3 @ X17 @ X16 @ X20 )
      | ( r3_lattice3 @ X17 @ ( sk_D_3 @ X20 @ X16 @ X17 ) @ X20 )
      | ( X16
        = ( k16_lattice3 @ X17 @ X20 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_lattice3 @ X17 @ X16 @ X20 )
      | ( m1_subset_1 @ ( sk_D_3 @ X20 @ X16 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( X16
        = ( k16_lattice3 @ X17 @ X20 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d16_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r3_lattice3 @ X7 @ X6 @ X8 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_lattices @ X7 @ X6 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r3_lattice3 @ X7 @ X6 @ X8 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_lattices @ X7 @ X6 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_lattices @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r4_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X15 @ X11 @ X12 ) @ X15 )
      | ( r4_lattice3 @ X12 @ X11 @ X15 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('59',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ X1 @ X0 ) )
      | ( ( sk_D_2 @ ( k2_tarski @ X1 @ X0 ) @ sk_B @ sk_A )
        = X1 )
      | ( ( sk_D_2 @ ( k2_tarski @ X1 @ X0 ) @ sk_B @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_lattices @ X12 @ ( sk_D_2 @ X15 @ X11 @ X12 ) @ X11 )
      | ( r4_lattice3 @ X12 @ X11 @ X15 )
      | ~ ( l3_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ( ( sk_D_2 @ ( k2_tarski @ X0 @ X1 ) @ sk_B @ sk_A )
        = X1 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ X0 @ X1 ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( sk_D_2 @ ( k2_tarski @ X0 @ X1 ) @ sk_B @ sk_A )
        = X1 )
      | ~ ( r1_lattices @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ ( k2_tarski @ sk_B @ X0 ) @ sk_B @ sk_A )
        = X0 )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ X0 @ sk_B )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ sk_B @ X0 ) )
      | ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ sk_B @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    r4_lattice3 @ sk_A @ sk_B @ ( k2_tarski @ sk_B @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r4_lattice3 @ A @ B @ C ) )
             => ( ( k15_lattice3 @ A @ C )
                = B ) ) ) ) )).

thf('76',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( ( k15_lattice3 @ X25 @ X26 )
        = X24 )
      | ~ ( r4_lattice3 @ X25 @ X24 @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t41_lattice3])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( ( k15_lattice3 @ sk_A @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( k2_tarski @ sk_B @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) ) )
      = sk_B )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('84',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( k2_tarski @ sk_B @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k15_lattice3 @ sk_A @ ( k2_tarski @ sk_B @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) ) )
    = sk_B ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('89',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t38_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ B @ C )
             => ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) )
                & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) )).

thf('91',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r3_lattices @ X22 @ X21 @ ( k15_lattice3 @ X22 @ X23 ) )
      | ~ ( r2_hidden @ X21 @ X23 )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_lattice3])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ ( k15_lattice3 @ sk_A @ ( k2_tarski @ X0 @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,(
    r3_lattices @ sk_A @ ( sk_D_3 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['87','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_lattice3 @ X17 @ X16 @ X20 )
      | ~ ( r3_lattices @ X17 @ ( sk_D_3 @ X20 @ X16 @ X17 ) @ X16 )
      | ( X16
        = ( k16_lattice3 @ X17 @ X20 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v4_lattice3 @ X17 )
      | ~ ( v10_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_3 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['0','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LktrquxRRd
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:18:49 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 2.04/2.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.04/2.26  % Solved by: fo/fo7.sh
% 2.04/2.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.26  % done 2361 iterations in 1.776s
% 2.04/2.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.04/2.26  % SZS output start Refutation
% 2.04/2.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.04/2.26  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.04/2.26  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 2.04/2.26  thf(sk_C_type, type, sk_C: $i).
% 2.04/2.26  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.04/2.26  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.04/2.26  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.04/2.26  thf(sk_B_type, type, sk_B: $i).
% 2.04/2.26  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.04/2.26  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.04/2.26  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.26  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.04/2.26  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.04/2.26  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.04/2.26  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 2.04/2.26  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.04/2.26  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 2.04/2.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.04/2.26  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 2.04/2.26  thf(t42_lattice3, conjecture,
% 2.04/2.26    (![A:$i]:
% 2.04/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.26         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.26       ( ![B:$i]:
% 2.04/2.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26           ( ![C:$i]:
% 2.04/2.26             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 2.04/2.26               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 2.04/2.26  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.26    (~( ![A:$i]:
% 2.04/2.26        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.26            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.26          ( ![B:$i]:
% 2.04/2.26            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26              ( ![C:$i]:
% 2.04/2.26                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 2.04/2.26                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 2.04/2.26    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 2.04/2.26  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('2', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf(t34_lattice3, axiom,
% 2.04/2.26    (![A:$i]:
% 2.04/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.26         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.26       ( ![B:$i]:
% 2.04/2.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26           ( ![C:$i]:
% 2.04/2.26             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 2.04/2.26               ( ( r3_lattice3 @ A @ B @ C ) & 
% 2.04/2.26                 ( ![D:$i]:
% 2.04/2.26                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 2.04/2.26                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 2.04/2.26  thf('4', plain,
% 2.04/2.26      (![X16 : $i, X17 : $i, X20 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 2.04/2.26          | ~ (r3_lattice3 @ X17 @ X16 @ X20)
% 2.04/2.26          | (r3_lattice3 @ X17 @ (sk_D_3 @ X20 @ X16 @ X17) @ X20)
% 2.04/2.26          | ((X16) = (k16_lattice3 @ X17 @ X20))
% 2.04/2.26          | ~ (l3_lattices @ X17)
% 2.04/2.26          | ~ (v4_lattice3 @ X17)
% 2.04/2.26          | ~ (v10_lattices @ X17)
% 2.04/2.26          | (v2_struct_0 @ X17))),
% 2.04/2.26      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.04/2.26  thf('5', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (v10_lattices @ sk_A)
% 2.04/2.26          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.26          | (r3_lattice3 @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('sup-', [status(thm)], ['3', '4'])).
% 2.04/2.26  thf('6', plain, ((v10_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('7', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('8', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('9', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.26          | (r3_lattice3 @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 2.04/2.26  thf('10', plain,
% 2.04/2.26      (((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 2.04/2.26        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['2', '9'])).
% 2.04/2.26  thf('11', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('12', plain,
% 2.04/2.26      (((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 2.04/2.26  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('14', plain,
% 2.04/2.26      ((r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 2.04/2.26      inference('clc', [status(thm)], ['12', '13'])).
% 2.04/2.26  thf('15', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('17', plain,
% 2.04/2.26      (![X16 : $i, X17 : $i, X20 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 2.04/2.26          | ~ (r3_lattice3 @ X17 @ X16 @ X20)
% 2.04/2.26          | (m1_subset_1 @ (sk_D_3 @ X20 @ X16 @ X17) @ (u1_struct_0 @ X17))
% 2.04/2.26          | ((X16) = (k16_lattice3 @ X17 @ X20))
% 2.04/2.26          | ~ (l3_lattices @ X17)
% 2.04/2.26          | ~ (v4_lattice3 @ X17)
% 2.04/2.26          | ~ (v10_lattices @ X17)
% 2.04/2.26          | (v2_struct_0 @ X17))),
% 2.04/2.26      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.04/2.26  thf('18', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (v10_lattices @ sk_A)
% 2.04/2.26          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.26          | (m1_subset_1 @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('sup-', [status(thm)], ['16', '17'])).
% 2.04/2.26  thf('19', plain, ((v10_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('20', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('21', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('22', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.26          | (m1_subset_1 @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 2.04/2.26  thf('23', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['15', '22'])).
% 2.04/2.26  thf('24', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('25', plain,
% 2.04/2.26      (((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 2.04/2.26  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('27', plain,
% 2.04/2.26      ((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('clc', [status(thm)], ['25', '26'])).
% 2.04/2.26  thf(d16_lattice3, axiom,
% 2.04/2.26    (![A:$i]:
% 2.04/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.04/2.26       ( ![B:$i]:
% 2.04/2.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26           ( ![C:$i]:
% 2.04/2.26             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 2.04/2.26               ( ![D:$i]:
% 2.04/2.26                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 2.04/2.26  thf('28', plain,
% 2.04/2.26      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 2.04/2.26          | ~ (r3_lattice3 @ X7 @ X6 @ X8)
% 2.04/2.26          | ~ (r2_hidden @ X9 @ X8)
% 2.04/2.26          | (r1_lattices @ X7 @ X6 @ X9)
% 2.04/2.26          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 2.04/2.26          | ~ (l3_lattices @ X7)
% 2.04/2.26          | (v2_struct_0 @ X7))),
% 2.04/2.26      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.04/2.26  thf('29', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r1_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | ~ (r2_hidden @ X0 @ X1)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['27', '28'])).
% 2.04/2.26  thf('30', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('31', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r1_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | ~ (r2_hidden @ X0 @ X1)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X1))),
% 2.04/2.26      inference('demod', [status(thm)], ['29', '30'])).
% 2.04/2.26  thf('32', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (r2_hidden @ X0 @ sk_C)
% 2.04/2.26          | (r1_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['14', '31'])).
% 2.04/2.26  thf('33', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_A)
% 2.04/2.26        | (r1_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 2.04/2.26        | ~ (r2_hidden @ sk_B @ sk_C))),
% 2.04/2.26      inference('sup-', [status(thm)], ['1', '32'])).
% 2.04/2.26  thf('34', plain, ((r2_hidden @ sk_B @ sk_C)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('35', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_A)
% 2.04/2.26        | (r1_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 2.04/2.26      inference('demod', [status(thm)], ['33', '34'])).
% 2.04/2.26  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('37', plain,
% 2.04/2.26      ((r1_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 2.04/2.26      inference('clc', [status(thm)], ['35', '36'])).
% 2.04/2.26  thf('38', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('39', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('40', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('41', plain,
% 2.04/2.26      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 2.04/2.26          | ~ (r3_lattice3 @ X7 @ X6 @ X8)
% 2.04/2.26          | ~ (r2_hidden @ X9 @ X8)
% 2.04/2.26          | (r1_lattices @ X7 @ X6 @ X9)
% 2.04/2.26          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 2.04/2.26          | ~ (l3_lattices @ X7)
% 2.04/2.26          | (v2_struct_0 @ X7))),
% 2.04/2.26      inference('cnf', [status(esa)], [d16_lattice3])).
% 2.04/2.26  thf('42', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r1_lattices @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ~ (r2_hidden @ X0 @ X1)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['40', '41'])).
% 2.04/2.26  thf('43', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('44', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.04/2.26          | (r1_lattices @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ~ (r2_hidden @ X0 @ X1)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X1))),
% 2.04/2.26      inference('demod', [status(thm)], ['42', '43'])).
% 2.04/2.26  thf('45', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (r3_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ~ (r2_hidden @ sk_B @ X0)
% 2.04/2.26          | (r1_lattices @ sk_A @ sk_B @ sk_B)
% 2.04/2.26          | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['39', '44'])).
% 2.04/2.26  thf('46', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_A)
% 2.04/2.26        | (r1_lattices @ sk_A @ sk_B @ sk_B)
% 2.04/2.26        | ~ (r2_hidden @ sk_B @ sk_C))),
% 2.04/2.26      inference('sup-', [status(thm)], ['38', '45'])).
% 2.04/2.26  thf('47', plain, ((r2_hidden @ sk_B @ sk_C)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('48', plain,
% 2.04/2.26      (((v2_struct_0 @ sk_A) | (r1_lattices @ sk_A @ sk_B @ sk_B))),
% 2.04/2.26      inference('demod', [status(thm)], ['46', '47'])).
% 2.04/2.26  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('50', plain, ((r1_lattices @ sk_A @ sk_B @ sk_B)),
% 2.04/2.26      inference('clc', [status(thm)], ['48', '49'])).
% 2.04/2.26  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf(d17_lattice3, axiom,
% 2.04/2.26    (![A:$i]:
% 2.04/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.04/2.26       ( ![B:$i]:
% 2.04/2.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26           ( ![C:$i]:
% 2.04/2.26             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 2.04/2.26               ( ![D:$i]:
% 2.04/2.26                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 2.04/2.26  thf('52', plain,
% 2.04/2.26      (![X11 : $i, X12 : $i, X15 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 2.04/2.26          | (r2_hidden @ (sk_D_2 @ X15 @ X11 @ X12) @ X15)
% 2.04/2.26          | (r4_lattice3 @ X12 @ X11 @ X15)
% 2.04/2.26          | ~ (l3_lattices @ X12)
% 2.04/2.26          | (v2_struct_0 @ X12))),
% 2.04/2.26      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.04/2.26  thf('53', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | (r2_hidden @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0))),
% 2.04/2.26      inference('sup-', [status(thm)], ['51', '52'])).
% 2.04/2.26  thf('54', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('55', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | (r2_hidden @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0))),
% 2.04/2.26      inference('demod', [status(thm)], ['53', '54'])).
% 2.04/2.26  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('57', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((r2_hidden @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('clc', [status(thm)], ['55', '56'])).
% 2.04/2.26  thf(d2_tarski, axiom,
% 2.04/2.26    (![A:$i,B:$i,C:$i]:
% 2.04/2.26     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.04/2.26       ( ![D:$i]:
% 2.04/2.26         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.04/2.26  thf('58', plain,
% 2.04/2.26      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.04/2.26         (~ (r2_hidden @ X4 @ X2)
% 2.04/2.26          | ((X4) = (X3))
% 2.04/2.26          | ((X4) = (X0))
% 2.04/2.26          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.04/2.26      inference('cnf', [status(esa)], [d2_tarski])).
% 2.04/2.26  thf('59', plain,
% 2.04/2.26      (![X0 : $i, X3 : $i, X4 : $i]:
% 2.04/2.26         (((X4) = (X0))
% 2.04/2.26          | ((X4) = (X3))
% 2.04/2.26          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 2.04/2.26      inference('simplify', [status(thm)], ['58'])).
% 2.04/2.26  thf('60', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         ((r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ X1 @ X0))
% 2.04/2.26          | ((sk_D_2 @ (k2_tarski @ X1 @ X0) @ sk_B @ sk_A) = (X1))
% 2.04/2.26          | ((sk_D_2 @ (k2_tarski @ X1 @ X0) @ sk_B @ sk_A) = (X0)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['57', '59'])).
% 2.04/2.26  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('62', plain,
% 2.04/2.26      (![X11 : $i, X12 : $i, X15 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 2.04/2.26          | ~ (r1_lattices @ X12 @ (sk_D_2 @ X15 @ X11 @ X12) @ X11)
% 2.04/2.26          | (r4_lattice3 @ X12 @ X11 @ X15)
% 2.04/2.26          | ~ (l3_lattices @ X12)
% 2.04/2.26          | (v2_struct_0 @ X12))),
% 2.04/2.26      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.04/2.26  thf('63', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ~ (r1_lattices @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 2.04/2.26      inference('sup-', [status(thm)], ['61', '62'])).
% 2.04/2.26  thf('64', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('65', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ~ (r1_lattices @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_B))),
% 2.04/2.26      inference('demod', [status(thm)], ['63', '64'])).
% 2.04/2.26  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('67', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (r1_lattices @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('clc', [status(thm)], ['65', '66'])).
% 2.04/2.26  thf('68', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         (~ (r1_lattices @ sk_A @ X0 @ sk_B)
% 2.04/2.26          | ((sk_D_2 @ (k2_tarski @ X0 @ X1) @ sk_B @ sk_A) = (X1))
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ X0 @ X1))
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ X0 @ X1)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['60', '67'])).
% 2.04/2.26  thf('69', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i]:
% 2.04/2.26         ((r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ X0 @ X1))
% 2.04/2.26          | ((sk_D_2 @ (k2_tarski @ X0 @ X1) @ sk_B @ sk_A) = (X1))
% 2.04/2.26          | ~ (r1_lattices @ sk_A @ X0 @ sk_B))),
% 2.04/2.26      inference('simplify', [status(thm)], ['68'])).
% 2.04/2.26  thf('70', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (((sk_D_2 @ (k2_tarski @ sk_B @ X0) @ sk_B @ sk_A) = (X0))
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ sk_B @ X0)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['50', '69'])).
% 2.04/2.26  thf('71', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (r1_lattices @ sk_A @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('clc', [status(thm)], ['65', '66'])).
% 2.04/2.26  thf('72', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (r1_lattices @ sk_A @ X0 @ sk_B)
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ sk_B @ X0))
% 2.04/2.26          | (r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ sk_B @ X0)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['70', '71'])).
% 2.04/2.26  thf('73', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((r4_lattice3 @ sk_A @ sk_B @ (k2_tarski @ sk_B @ X0))
% 2.04/2.26          | ~ (r1_lattices @ sk_A @ X0 @ sk_B))),
% 2.04/2.26      inference('simplify', [status(thm)], ['72'])).
% 2.04/2.26  thf('74', plain,
% 2.04/2.26      ((r4_lattice3 @ sk_A @ sk_B @ 
% 2.04/2.26        (k2_tarski @ sk_B @ (sk_D_3 @ sk_C @ sk_B @ sk_A)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['37', '73'])).
% 2.04/2.26  thf('75', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf(t41_lattice3, axiom,
% 2.04/2.26    (![A:$i]:
% 2.04/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.26         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.26       ( ![B:$i]:
% 2.04/2.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26           ( ![C:$i]:
% 2.04/2.26             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 2.04/2.26               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 2.04/2.26  thf('76', plain,
% 2.04/2.26      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 2.04/2.26          | ((k15_lattice3 @ X25 @ X26) = (X24))
% 2.04/2.26          | ~ (r4_lattice3 @ X25 @ X24 @ X26)
% 2.04/2.26          | ~ (r2_hidden @ X24 @ X26)
% 2.04/2.26          | ~ (l3_lattices @ X25)
% 2.04/2.26          | ~ (v4_lattice3 @ X25)
% 2.04/2.26          | ~ (v10_lattices @ X25)
% 2.04/2.26          | (v2_struct_0 @ X25))),
% 2.04/2.26      inference('cnf', [status(esa)], [t41_lattice3])).
% 2.04/2.26  thf('77', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (v10_lattices @ sk_A)
% 2.04/2.26          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | ~ (r2_hidden @ sk_B @ X0)
% 2.04/2.26          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['75', '76'])).
% 2.04/2.26  thf('78', plain, ((v10_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('79', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('80', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('81', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (r2_hidden @ sk_B @ X0)
% 2.04/2.26          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 2.04/2.26          | ((k15_lattice3 @ sk_A @ X0) = (sk_B)))),
% 2.04/2.26      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 2.04/2.26  thf('82', plain,
% 2.04/2.26      ((((k15_lattice3 @ sk_A @ 
% 2.04/2.26          (k2_tarski @ sk_B @ (sk_D_3 @ sk_C @ sk_B @ sk_A))) = (sk_B))
% 2.04/2.26        | ~ (r2_hidden @ sk_B @ 
% 2.04/2.26             (k2_tarski @ sk_B @ (sk_D_3 @ sk_C @ sk_B @ sk_A)))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['74', '81'])).
% 2.04/2.26  thf('83', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.04/2.26         (((X1) != (X3))
% 2.04/2.26          | (r2_hidden @ X1 @ X2)
% 2.04/2.26          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.04/2.26      inference('cnf', [status(esa)], [d2_tarski])).
% 2.04/2.26  thf('84', plain,
% 2.04/2.26      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 2.04/2.26      inference('simplify', [status(thm)], ['83'])).
% 2.04/2.26  thf('85', plain,
% 2.04/2.26      ((((k15_lattice3 @ sk_A @ 
% 2.04/2.26          (k2_tarski @ sk_B @ (sk_D_3 @ sk_C @ sk_B @ sk_A))) = (sk_B))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('demod', [status(thm)], ['82', '84'])).
% 2.04/2.26  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('87', plain,
% 2.04/2.26      (((k15_lattice3 @ sk_A @ 
% 2.04/2.26         (k2_tarski @ sk_B @ (sk_D_3 @ sk_C @ sk_B @ sk_A))) = (sk_B))),
% 2.04/2.26      inference('clc', [status(thm)], ['85', '86'])).
% 2.04/2.26  thf('88', plain,
% 2.04/2.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.04/2.26         (((X1) != (X0))
% 2.04/2.26          | (r2_hidden @ X1 @ X2)
% 2.04/2.26          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 2.04/2.26      inference('cnf', [status(esa)], [d2_tarski])).
% 2.04/2.26  thf('89', plain,
% 2.04/2.26      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 2.04/2.26      inference('simplify', [status(thm)], ['88'])).
% 2.04/2.26  thf('90', plain,
% 2.04/2.26      ((m1_subset_1 @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('clc', [status(thm)], ['25', '26'])).
% 2.04/2.26  thf(t38_lattice3, axiom,
% 2.04/2.26    (![A:$i]:
% 2.04/2.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.04/2.26         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.04/2.26       ( ![B:$i]:
% 2.04/2.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.04/2.26           ( ![C:$i]:
% 2.04/2.26             ( ( r2_hidden @ B @ C ) =>
% 2.04/2.26               ( ( r3_lattices @ A @ B @ ( k15_lattice3 @ A @ C ) ) & 
% 2.04/2.26                 ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ B ) ) ) ) ) ) ))).
% 2.04/2.26  thf('91', plain,
% 2.04/2.26      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.04/2.26          | (r3_lattices @ X22 @ X21 @ (k15_lattice3 @ X22 @ X23))
% 2.04/2.26          | ~ (r2_hidden @ X21 @ X23)
% 2.04/2.26          | ~ (l3_lattices @ X22)
% 2.04/2.26          | ~ (v4_lattice3 @ X22)
% 2.04/2.26          | ~ (v10_lattices @ X22)
% 2.04/2.26          | (v2_struct_0 @ X22))),
% 2.04/2.26      inference('cnf', [status(esa)], [t38_lattice3])).
% 2.04/2.26  thf('92', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (v10_lattices @ sk_A)
% 2.04/2.26          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | (r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.26             (k15_lattice3 @ sk_A @ X0)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['90', '91'])).
% 2.04/2.26  thf('93', plain, ((v10_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('94', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('95', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('96', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0)
% 2.04/2.26          | (r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.26             (k15_lattice3 @ sk_A @ X0)))),
% 2.04/2.26      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 2.04/2.26  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('98', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.26           (k15_lattice3 @ sk_A @ X0))
% 2.04/2.26          | ~ (r2_hidden @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ X0))),
% 2.04/2.26      inference('clc', [status(thm)], ['96', '97'])).
% 2.04/2.26  thf('99', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ 
% 2.04/2.26          (k15_lattice3 @ sk_A @ 
% 2.04/2.26           (k2_tarski @ X0 @ (sk_D_3 @ sk_C @ sk_B @ sk_A))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['89', '98'])).
% 2.04/2.26  thf('100', plain,
% 2.04/2.26      ((r3_lattices @ sk_A @ (sk_D_3 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 2.04/2.26      inference('sup+', [status(thm)], ['87', '99'])).
% 2.04/2.26  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('102', plain,
% 2.04/2.26      (![X16 : $i, X17 : $i, X20 : $i]:
% 2.04/2.26         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 2.04/2.26          | ~ (r3_lattice3 @ X17 @ X16 @ X20)
% 2.04/2.26          | ~ (r3_lattices @ X17 @ (sk_D_3 @ X20 @ X16 @ X17) @ X16)
% 2.04/2.26          | ((X16) = (k16_lattice3 @ X17 @ X20))
% 2.04/2.26          | ~ (l3_lattices @ X17)
% 2.04/2.26          | ~ (v4_lattice3 @ X17)
% 2.04/2.26          | ~ (v10_lattices @ X17)
% 2.04/2.26          | (v2_struct_0 @ X17))),
% 2.04/2.26      inference('cnf', [status(esa)], [t34_lattice3])).
% 2.04/2.26  thf('103', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ~ (v10_lattices @ sk_A)
% 2.04/2.26          | ~ (v4_lattice3 @ sk_A)
% 2.04/2.26          | ~ (l3_lattices @ sk_A)
% 2.04/2.26          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.26          | ~ (r3_lattices @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('sup-', [status(thm)], ['101', '102'])).
% 2.04/2.26  thf('104', plain, ((v10_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('105', plain, ((v4_lattice3 @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('106', plain, ((l3_lattices @ sk_A)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('107', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         ((v2_struct_0 @ sk_A)
% 2.04/2.26          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 2.04/2.26          | ~ (r3_lattices @ sk_A @ (sk_D_3 @ X0 @ sk_B @ sk_A) @ sk_B)
% 2.04/2.26          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 2.04/2.26      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 2.04/2.26  thf('108', plain,
% 2.04/2.26      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 2.04/2.26        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 2.04/2.26        | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('sup-', [status(thm)], ['100', '107'])).
% 2.04/2.26  thf('109', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('110', plain,
% 2.04/2.26      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 2.04/2.26      inference('demod', [status(thm)], ['108', '109'])).
% 2.04/2.26  thf('111', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 2.04/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.26  thf('112', plain, ((v2_struct_0 @ sk_A)),
% 2.04/2.26      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 2.04/2.26  thf('113', plain, ($false), inference('demod', [status(thm)], ['0', '112'])).
% 2.04/2.26  
% 2.04/2.26  % SZS output end Refutation
% 2.04/2.26  
% 2.04/2.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
