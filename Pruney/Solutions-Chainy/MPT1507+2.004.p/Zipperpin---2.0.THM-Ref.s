%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4s3fbnCfOn

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 120 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  652 (1878 expanded)
%              Number of equality atoms :   20 (  70 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t41_lattice3,conjecture,(
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
                  & ( r4_lattice3 @ A @ B @ C ) )
               => ( ( k15_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r4_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d21_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
           => ( ( C
                = ( k15_lattice3 @ A @ B ) )
            <=> ( ( r4_lattice3 @ A @ C @ B )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r4_lattice3 @ A @ D @ B )
                     => ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r4_lattice3 @ X5 @ X6 @ X7 )
      | ( r4_lattice3 @ X5 @ ( sk_D_1 @ X6 @ X7 @ X5 ) @ X7 )
      | ( X6
        = ( k15_lattice3 @ X5 @ X7 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6
        = ( k15_lattice3 @ X5 @ X7 ) )
      | ( r4_lattice3 @ X5 @ ( sk_D_1 @ X6 @ X7 @ X5 ) @ X7 )
      | ~ ( r4_lattice3 @ X5 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( r4_lattice3 @ sk_A @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ sk_C ) )
    | ( r4_lattice3 @ sk_A @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ( k15_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r4_lattice3 @ sk_A @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r4_lattice3 @ sk_A @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    r4_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r4_lattice3 @ X5 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_D_1 @ X6 @ X7 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ( X6
        = ( k15_lattice3 @ X5 @ X7 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6
        = ( k15_lattice3 @ X5 @ X7 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X6 @ X7 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( r4_lattice3 @ X5 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ( sk_B
      = ( k15_lattice3 @ sk_A @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ( k15_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r4_lattice3 @ X1 @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_lattices @ X1 @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r4_lattice3 @ sk_A @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_lattices @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','34'])).

thf('36',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_lattices @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r4_lattice3 @ X5 @ X6 @ X7 )
      | ~ ( r1_lattices @ X5 @ X6 @ ( sk_D_1 @ X6 @ X7 @ X5 ) )
      | ( X6
        = ( k15_lattice3 @ X5 @ X7 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6
        = ( k15_lattice3 @ X5 @ X7 ) )
      | ~ ( r1_lattices @ X5 @ X6 @ ( sk_D_1 @ X6 @ X7 @ X5 ) )
      | ~ ( r4_lattice3 @ X5 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v4_lattice3 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r4_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r4_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k15_lattice3 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47'])).

thf('49',plain,(
    ( k15_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4s3fbnCfOn
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:58:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 41 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.20/0.49  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.49  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(t41_lattice3, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.49               ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( r2_hidden @ B @ C ) & ( r4_lattice3 @ A @ B @ C ) ) =>
% 0.20/0.49                  ( ( k15_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t41_lattice3])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain, ((r4_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d21_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.20/0.49           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49         ( ![B:$i,C:$i]:
% 0.20/0.49           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.20/0.49               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.20/0.49                 ( ![D:$i]:
% 0.20/0.49                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.20/0.49                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (r4_lattice3 @ X5 @ X6 @ X7)
% 0.20/0.49          | (r4_lattice3 @ X5 @ (sk_D_1 @ X6 @ X7 @ X5) @ X7)
% 0.20/0.49          | ((X6) = (k15_lattice3 @ X5 @ X7))
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (((X6) = (k15_lattice3 @ X5 @ X7))
% 0.20/0.49          | (r4_lattice3 @ X5 @ (sk_D_1 @ X6 @ X7 @ X5) @ X7)
% 0.20/0.49          | ~ (r4_lattice3 @ X5 @ X6 @ X7)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v10_lattices @ sk_A)
% 0.20/0.49          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.49          | ~ (l3_lattices @ sk_A)
% 0.20/0.49          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (r4_lattice3 @ sk_A @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0)
% 0.20/0.49          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.49  thf('7', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (r4_lattice3 @ sk_A @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ X0)
% 0.20/0.49          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((sk_B) = (k15_lattice3 @ sk_A @ sk_C))
% 0.20/0.49        | (r4_lattice3 @ sk_A @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.49  thf('12', plain, (((k15_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((r4_lattice3 @ sk_A @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((r4_lattice3 @ sk_A @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ sk_C)),
% 0.20/0.49      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, ((r4_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (r4_lattice3 @ X5 @ X6 @ X7)
% 0.20/0.49          | (m1_subset_1 @ (sk_D_1 @ X6 @ X7 @ X5) @ (u1_struct_0 @ X5))
% 0.20/0.49          | ((X6) = (k15_lattice3 @ X5 @ X7))
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (((X6) = (k15_lattice3 @ X5 @ X7))
% 0.20/0.49          | (m1_subset_1 @ (sk_D_1 @ X6 @ X7 @ X5) @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (r4_lattice3 @ X5 @ X6 @ X7)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v10_lattices @ sk_A)
% 0.20/0.49          | ~ (v4_lattice3 @ sk_A)
% 0.20/0.49          | ~ (l3_lattices @ sk_A)
% 0.20/0.49          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (m1_subset_1 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.49  thf('21', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (r4_lattice3 @ sk_A @ sk_B @ X0)
% 0.20/0.49          | (m1_subset_1 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | ((sk_B) = (k15_lattice3 @ sk_A @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((((sk_B) = (k15_lattice3 @ sk_A @ sk_C))
% 0.20/0.49        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '24'])).
% 0.20/0.49  thf('26', plain, (((k15_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf(d17_lattice3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (r4_lattice3 @ X1 @ X0 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.49          | (r1_lattices @ X1 @ X3 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l3_lattices @ X1)
% 0.20/0.49          | (v2_struct_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l3_lattices @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_lattices @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_C @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | ~ (r4_lattice3 @ sk_A @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (r1_lattices @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_C @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | ~ (r4_lattice3 @ sk_A @ (sk_D_1 @ sk_B @ sk_C @ sk_A) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ sk_C)
% 0.20/0.49          | (r1_lattices @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_C @ sk_A))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_lattices @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_C @ sk_A))
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '34'])).
% 0.20/0.49  thf('36', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_lattices @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_C @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((r1_lattices @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_C @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (r4_lattice3 @ X5 @ X6 @ X7)
% 0.20/0.49          | ~ (r1_lattices @ X5 @ X6 @ (sk_D_1 @ X6 @ X7 @ X5))
% 0.20/0.49          | ((X6) = (k15_lattice3 @ X5 @ X7))
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (((X6) = (k15_lattice3 @ X5 @ X7))
% 0.20/0.49          | ~ (r1_lattices @ X5 @ X6 @ (sk_D_1 @ X6 @ X7 @ X5))
% 0.20/0.49          | ~ (r4_lattice3 @ X5 @ X6 @ X7)
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.49          | ~ (l3_lattices @ X5)
% 0.20/0.49          | ~ (v4_lattice3 @ X5)
% 0.20/0.49          | ~ (v10_lattices @ X5)
% 0.20/0.49          | (v2_struct_0 @ X5))),
% 0.20/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v10_lattices @ sk_A)
% 0.20/0.49        | ~ (v4_lattice3 @ sk_A)
% 0.20/0.49        | ~ (l3_lattices @ sk_A)
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (r4_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.20/0.49        | ((sk_B) = (k15_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.49  thf('43', plain, ((v10_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('44', plain, ((v4_lattice3 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain, ((l3_lattices @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain, ((r4_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A) | ((sk_B) = (k15_lattice3 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['42', '43', '44', '45', '46', '47'])).
% 0.20/0.49  thf('49', plain, (((k15_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
