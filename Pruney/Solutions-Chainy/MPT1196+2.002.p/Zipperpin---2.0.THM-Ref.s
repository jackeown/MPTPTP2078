%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oAy9f88YVc

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:30 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 121 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  586 (1779 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(t22_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_lattices @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l2_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k1_lattices @ X10 @ X9 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattices])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( l2_lattices @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('7',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf(d8_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v8_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C )
                  = C ) ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v8_lattices @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( ( k1_lattices @ X3 @ ( k2_lattices @ X3 @ X5 @ X4 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ) @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
        = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ) @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
        = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ) @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
        = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ) @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v9_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) )
                  = B ) ) ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v9_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k2_lattices @ X6 @ X8 @ ( k1_lattices @ X6 @ X8 @ X7 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_2 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_2 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_2 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['19','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k1_lattices @ A @ B @ C )
                  = C ) ) ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
       != X2 )
      | ( r1_lattices @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
     != ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( r1_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
     != ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k1_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
 != ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oAy9f88YVc
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.92/3.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.92/3.10  % Solved by: fo/fo7.sh
% 2.92/3.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.92/3.10  % done 809 iterations in 2.641s
% 2.92/3.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.92/3.10  % SZS output start Refutation
% 2.92/3.10  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 2.92/3.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.92/3.10  thf(sk_A_type, type, sk_A: $i).
% 2.92/3.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.92/3.10  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.92/3.10  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 2.92/3.10  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.92/3.10  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 2.92/3.10  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 2.92/3.10  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 2.92/3.10  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 2.92/3.10  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 2.92/3.10  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 2.92/3.10  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.92/3.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.92/3.10  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.92/3.10  thf(t22_lattices, conjecture,
% 2.92/3.10    (![A:$i]:
% 2.92/3.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_lattices @ A ) & 
% 2.92/3.10         ( v6_lattices @ A ) & ( v8_lattices @ A ) & ( v9_lattices @ A ) & 
% 2.92/3.10         ( l3_lattices @ A ) ) =>
% 2.92/3.10       ( ![B:$i]:
% 2.92/3.10         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10           ( ![C:$i]:
% 2.92/3.10             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10               ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ) ))).
% 2.92/3.10  thf(zf_stmt_0, negated_conjecture,
% 2.92/3.10    (~( ![A:$i]:
% 2.92/3.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_lattices @ A ) & 
% 2.92/3.10            ( v6_lattices @ A ) & ( v8_lattices @ A ) & ( v9_lattices @ A ) & 
% 2.92/3.10            ( l3_lattices @ A ) ) =>
% 2.92/3.10          ( ![B:$i]:
% 2.92/3.10            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10              ( ![C:$i]:
% 2.92/3.10                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10                  ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ) ) )),
% 2.92/3.10    inference('cnf.neg', [status(esa)], [t22_lattices])).
% 2.92/3.10  thf('0', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf(dt_k1_lattices, axiom,
% 2.92/3.10    (![A:$i,B:$i,C:$i]:
% 2.92/3.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) & 
% 2.92/3.10         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 2.92/3.10         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.92/3.10       ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 2.92/3.10  thf('3', plain,
% 2.92/3.10      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.92/3.10         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 2.92/3.10          | ~ (l2_lattices @ X10)
% 2.92/3.10          | (v2_struct_0 @ X10)
% 2.92/3.10          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.92/3.10          | (m1_subset_1 @ (k1_lattices @ X10 @ X9 @ X11) @ (u1_struct_0 @ X10)))),
% 2.92/3.10      inference('cnf', [status(esa)], [dt_k1_lattices])).
% 2.92/3.10  thf('4', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 2.92/3.10           (u1_struct_0 @ sk_A))
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | (v2_struct_0 @ sk_A)
% 2.92/3.10          | ~ (l2_lattices @ sk_A))),
% 2.92/3.10      inference('sup-', [status(thm)], ['2', '3'])).
% 2.92/3.10  thf('5', plain, ((l3_lattices @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf(dt_l3_lattices, axiom,
% 2.92/3.10    (![A:$i]:
% 2.92/3.10     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 2.92/3.10  thf('6', plain, (![X12 : $i]: ((l2_lattices @ X12) | ~ (l3_lattices @ X12))),
% 2.92/3.10      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 2.92/3.10  thf('7', plain, ((l2_lattices @ sk_A)),
% 2.92/3.10      inference('sup-', [status(thm)], ['5', '6'])).
% 2.92/3.10  thf('8', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 2.92/3.10           (u1_struct_0 @ sk_A))
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | (v2_struct_0 @ sk_A))),
% 2.92/3.10      inference('demod', [status(thm)], ['4', '7'])).
% 2.92/3.10  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('10', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | (m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 2.92/3.10             (u1_struct_0 @ sk_A)))),
% 2.92/3.10      inference('clc', [status(thm)], ['8', '9'])).
% 2.92/3.10  thf('11', plain,
% 2.92/3.10      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ 
% 2.92/3.10        (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('sup-', [status(thm)], ['1', '10'])).
% 2.92/3.10  thf(d8_lattices, axiom,
% 2.92/3.10    (![A:$i]:
% 2.92/3.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.92/3.10       ( ( v8_lattices @ A ) <=>
% 2.92/3.10         ( ![B:$i]:
% 2.92/3.10           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10             ( ![C:$i]:
% 2.92/3.10               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 2.92/3.10                   ( C ) ) ) ) ) ) ) ))).
% 2.92/3.10  thf('12', plain,
% 2.92/3.10      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.92/3.10         (~ (v8_lattices @ X3)
% 2.92/3.10          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 2.92/3.10          | ((k1_lattices @ X3 @ (k2_lattices @ X3 @ X5 @ X4) @ X4) = (X4))
% 2.92/3.10          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 2.92/3.10          | ~ (l3_lattices @ X3)
% 2.92/3.10          | (v2_struct_0 @ X3))),
% 2.92/3.10      inference('cnf', [status(esa)], [d8_lattices])).
% 2.92/3.10  thf('13', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((v2_struct_0 @ sk_A)
% 2.92/3.10          | ~ (l3_lattices @ sk_A)
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | ((k1_lattices @ sk_A @ 
% 2.92/3.10              (k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2)) @ 
% 2.92/3.10              (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10              = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10          | ~ (v8_lattices @ sk_A))),
% 2.92/3.10      inference('sup-', [status(thm)], ['11', '12'])).
% 2.92/3.10  thf('14', plain, ((l3_lattices @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('15', plain, ((v8_lattices @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('16', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((v2_struct_0 @ sk_A)
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | ((k1_lattices @ sk_A @ 
% 2.92/3.10              (k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2)) @ 
% 2.92/3.10              (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10              = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2)))),
% 2.92/3.10      inference('demod', [status(thm)], ['13', '14', '15'])).
% 2.92/3.10  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('18', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         (((k1_lattices @ sk_A @ 
% 2.92/3.10            (k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2)) @ 
% 2.92/3.10            (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10            = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.10      inference('clc', [status(thm)], ['16', '17'])).
% 2.92/3.10  thf('19', plain,
% 2.92/3.10      (((k1_lattices @ sk_A @ 
% 2.92/3.10         (k2_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2)) @ 
% 2.92/3.10         (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10         = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 2.92/3.10      inference('sup-', [status(thm)], ['0', '18'])).
% 2.92/3.10  thf('20', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('21', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf(d9_lattices, axiom,
% 2.92/3.10    (![A:$i]:
% 2.92/3.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.92/3.10       ( ( v9_lattices @ A ) <=>
% 2.92/3.10         ( ![B:$i]:
% 2.92/3.10           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10             ( ![C:$i]:
% 2.92/3.10               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 2.92/3.10                   ( B ) ) ) ) ) ) ) ))).
% 2.92/3.10  thf('22', plain,
% 2.92/3.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.92/3.10         (~ (v9_lattices @ X6)
% 2.92/3.10          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 2.92/3.10          | ((k2_lattices @ X6 @ X8 @ (k1_lattices @ X6 @ X8 @ X7)) = (X8))
% 2.92/3.10          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 2.92/3.10          | ~ (l3_lattices @ X6)
% 2.92/3.10          | (v2_struct_0 @ X6))),
% 2.92/3.10      inference('cnf', [status(esa)], [d9_lattices])).
% 2.92/3.10  thf('23', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((v2_struct_0 @ sk_A)
% 2.92/3.10          | ~ (l3_lattices @ sk_A)
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_2))
% 2.92/3.10              = (X0))
% 2.92/3.10          | ~ (v9_lattices @ sk_A))),
% 2.92/3.10      inference('sup-', [status(thm)], ['21', '22'])).
% 2.92/3.10  thf('24', plain, ((l3_lattices @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('25', plain, ((v9_lattices @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('26', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((v2_struct_0 @ sk_A)
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_2))
% 2.92/3.10              = (X0)))),
% 2.92/3.10      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.92/3.10  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('28', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_2))
% 2.92/3.10            = (X0))
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.10      inference('clc', [status(thm)], ['26', '27'])).
% 2.92/3.10  thf('29', plain,
% 2.92/3.10      (((k2_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10         = (sk_B_2))),
% 2.92/3.10      inference('sup-', [status(thm)], ['20', '28'])).
% 2.92/3.10  thf('30', plain,
% 2.92/3.10      (((k1_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10         = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 2.92/3.10      inference('demod', [status(thm)], ['19', '29'])).
% 2.92/3.10  thf('31', plain,
% 2.92/3.10      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ 
% 2.92/3.10        (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('sup-', [status(thm)], ['1', '10'])).
% 2.92/3.10  thf('32', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf(d3_lattices, axiom,
% 2.92/3.10    (![A:$i]:
% 2.92/3.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 2.92/3.10       ( ![B:$i]:
% 2.92/3.10         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10           ( ![C:$i]:
% 2.92/3.10             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.10               ( ( r1_lattices @ A @ B @ C ) <=>
% 2.92/3.10                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 2.92/3.10  thf('33', plain,
% 2.92/3.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.10         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 2.92/3.10          | ((k1_lattices @ X1 @ X0 @ X2) != (X2))
% 2.92/3.10          | (r1_lattices @ X1 @ X0 @ X2)
% 2.92/3.10          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 2.92/3.10          | ~ (l2_lattices @ X1)
% 2.92/3.10          | (v2_struct_0 @ X1))),
% 2.92/3.10      inference('cnf', [status(esa)], [d3_lattices])).
% 2.92/3.10  thf('34', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((v2_struct_0 @ sk_A)
% 2.92/3.10          | ~ (l2_lattices @ sk_A)
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 2.92/3.10          | ((k1_lattices @ sk_A @ sk_B_2 @ X0) != (X0)))),
% 2.92/3.10      inference('sup-', [status(thm)], ['32', '33'])).
% 2.92/3.10  thf('35', plain, ((l2_lattices @ sk_A)),
% 2.92/3.10      inference('sup-', [status(thm)], ['5', '6'])).
% 2.92/3.10  thf('36', plain,
% 2.92/3.10      (![X0 : $i]:
% 2.92/3.10         ((v2_struct_0 @ sk_A)
% 2.92/3.10          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.92/3.10          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 2.92/3.10          | ((k1_lattices @ sk_A @ sk_B_2 @ X0) != (X0)))),
% 2.92/3.10      inference('demod', [status(thm)], ['34', '35'])).
% 2.92/3.10  thf('37', plain,
% 2.92/3.10      ((((k1_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10          != (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10        | (r1_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10        | (v2_struct_0 @ sk_A))),
% 2.92/3.10      inference('sup-', [status(thm)], ['31', '36'])).
% 2.92/3.10  thf('38', plain,
% 2.92/3.10      (~ (r1_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('39', plain,
% 2.92/3.10      (((v2_struct_0 @ sk_A)
% 2.92/3.10        | ((k1_lattices @ sk_A @ sk_B_2 @ 
% 2.92/3.10            (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10            != (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2)))),
% 2.92/3.10      inference('clc', [status(thm)], ['37', '38'])).
% 2.92/3.10  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.10  thf('41', plain,
% 2.92/3.10      (((k1_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 2.92/3.10         != (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 2.92/3.10      inference('clc', [status(thm)], ['39', '40'])).
% 2.92/3.10  thf('42', plain, ($false),
% 2.92/3.10      inference('simplify_reflect-', [status(thm)], ['30', '41'])).
% 2.92/3.10  
% 2.92/3.10  % SZS output end Refutation
% 2.92/3.10  
% 2.92/3.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
