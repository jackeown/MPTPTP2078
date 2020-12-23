%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D5JgS2wvhv

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:36 EST 2020

% Result     : Theorem 0.32s
% Output     : Refutation 0.32s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 147 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  633 (1475 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v14_lattices_type,type,(
    v14_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(t45_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v14_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v14_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
       != X6 )
      | ( r1_lattices @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( l2_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('8',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k6_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l2_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_lattices])).

thf(d17_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( ( v14_lattices @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( B
                = ( k6_lattices @ A ) )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( ( k1_lattices @ A @ B @ C )
                      = B )
                    & ( ( k1_lattices @ A @ C @ B )
                      = B ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v14_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( X2
       != ( k6_lattices @ X1 ) )
      | ( ( k1_lattices @ X1 @ X3 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d17_lattices])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l2_lattices @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ X3 @ ( k6_lattices @ X1 ) )
        = ( k6_lattices @ X1 ) )
      | ~ ( m1_subset_1 @ ( k6_lattices @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v14_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v14_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ X1 @ ( k6_lattices @ X0 ) )
        = ( k6_lattices @ X0 ) )
      | ~ ( v14_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( v14_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('24',plain,(
    v14_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
      = ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    = ( k6_lattices @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k6_lattices @ sk_A )
     != ( k6_lattices @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','27'])).

thf('29',plain,(
    r1_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r3_lattices @ X10 @ X9 @ X11 )
      | ~ ( r1_lattices @ X10 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','38','44','50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k6_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ ( k6_lattices @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ( m1_subset_1 @ ( k6_lattices @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('60',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D5JgS2wvhv
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.32/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.32/0.52  % Solved by: fo/fo7.sh
% 0.32/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.32/0.52  % done 74 iterations in 0.058s
% 0.32/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.32/0.52  % SZS output start Refutation
% 0.32/0.52  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.32/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.32/0.52  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.32/0.52  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.32/0.52  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.32/0.52  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.32/0.52  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.32/0.52  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.32/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.32/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.32/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.32/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.32/0.52  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.32/0.52  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.32/0.52  thf(v14_lattices_type, type, v14_lattices: $i > $o).
% 0.32/0.52  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.32/0.52  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.32/0.52  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.32/0.52  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.32/0.52  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.32/0.52  thf(t45_lattices, conjecture,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.32/0.52         ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.32/0.52       ( ![B:$i]:
% 0.32/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.32/0.52           ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) ))).
% 0.32/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.32/0.52    (~( ![A:$i]:
% 0.32/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.32/0.52            ( v14_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.32/0.52          ( ![B:$i]:
% 0.32/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.32/0.52              ( r3_lattices @ A @ B @ ( k6_lattices @ A ) ) ) ) ) )),
% 0.32/0.52    inference('cnf.neg', [status(esa)], [t45_lattices])).
% 0.32/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf(dt_k6_lattices, axiom,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.32/0.52       ( m1_subset_1 @ ( k6_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.32/0.52  thf('1', plain,
% 0.32/0.52      (![X7 : $i]:
% 0.32/0.52         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.32/0.52          | ~ (l2_lattices @ X7)
% 0.32/0.52          | (v2_struct_0 @ X7))),
% 0.32/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.32/0.52  thf('2', plain,
% 0.32/0.52      (![X7 : $i]:
% 0.32/0.52         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.32/0.52          | ~ (l2_lattices @ X7)
% 0.32/0.52          | (v2_struct_0 @ X7))),
% 0.32/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.32/0.52  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf(d3_lattices, axiom,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.32/0.52       ( ![B:$i]:
% 0.32/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.32/0.52           ( ![C:$i]:
% 0.32/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.32/0.52               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.32/0.52                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.32/0.52  thf('4', plain,
% 0.32/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.32/0.52         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.32/0.52          | ((k1_lattices @ X5 @ X4 @ X6) != (X6))
% 0.32/0.52          | (r1_lattices @ X5 @ X4 @ X6)
% 0.32/0.52          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.32/0.52          | ~ (l2_lattices @ X5)
% 0.32/0.52          | (v2_struct_0 @ X5))),
% 0.32/0.52      inference('cnf', [status(esa)], [d3_lattices])).
% 0.32/0.52  thf('5', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         ((v2_struct_0 @ sk_A)
% 0.32/0.52          | ~ (l2_lattices @ sk_A)
% 0.32/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.32/0.52          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.32/0.52          | ((k1_lattices @ sk_A @ sk_B @ X0) != (X0)))),
% 0.32/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.32/0.52  thf('6', plain, ((l3_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf(dt_l3_lattices, axiom,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.32/0.52  thf('7', plain, (![X8 : $i]: ((l2_lattices @ X8) | ~ (l3_lattices @ X8))),
% 0.32/0.52      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.32/0.52  thf('8', plain, ((l2_lattices @ sk_A)),
% 0.32/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.32/0.52  thf('9', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         ((v2_struct_0 @ sk_A)
% 0.32/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.32/0.52          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.32/0.52          | ((k1_lattices @ sk_A @ sk_B @ X0) != (X0)))),
% 0.32/0.52      inference('demod', [status(thm)], ['5', '8'])).
% 0.32/0.52  thf('10', plain,
% 0.32/0.52      (((v2_struct_0 @ sk_A)
% 0.32/0.52        | ~ (l2_lattices @ sk_A)
% 0.32/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52            != (k6_lattices @ sk_A))
% 0.32/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52        | (v2_struct_0 @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['2', '9'])).
% 0.32/0.52  thf('11', plain, ((l2_lattices @ sk_A)),
% 0.32/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.32/0.52  thf('12', plain,
% 0.32/0.52      (((v2_struct_0 @ sk_A)
% 0.32/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52            != (k6_lattices @ sk_A))
% 0.32/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52        | (v2_struct_0 @ sk_A))),
% 0.32/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.32/0.52  thf('13', plain,
% 0.32/0.52      (((r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52            != (k6_lattices @ sk_A))
% 0.32/0.52        | (v2_struct_0 @ sk_A))),
% 0.32/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.32/0.52  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('15', plain,
% 0.32/0.52      ((((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52          != (k6_lattices @ sk_A))
% 0.32/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.32/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.32/0.52  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('17', plain,
% 0.32/0.52      (![X7 : $i]:
% 0.32/0.52         ((m1_subset_1 @ (k6_lattices @ X7) @ (u1_struct_0 @ X7))
% 0.32/0.52          | ~ (l2_lattices @ X7)
% 0.32/0.52          | (v2_struct_0 @ X7))),
% 0.32/0.52      inference('cnf', [status(esa)], [dt_k6_lattices])).
% 0.32/0.52  thf(d17_lattices, axiom,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.32/0.52       ( ( v14_lattices @ A ) =>
% 0.32/0.52         ( ![B:$i]:
% 0.32/0.52           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.32/0.52             ( ( ( B ) = ( k6_lattices @ A ) ) <=>
% 0.32/0.52               ( ![C:$i]:
% 0.32/0.52                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.32/0.52                   ( ( ( k1_lattices @ A @ B @ C ) = ( B ) ) & 
% 0.32/0.52                     ( ( k1_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 0.32/0.52  thf('18', plain,
% 0.32/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.32/0.52         (~ (v14_lattices @ X1)
% 0.32/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.32/0.52          | ((X2) != (k6_lattices @ X1))
% 0.32/0.52          | ((k1_lattices @ X1 @ X3 @ X2) = (X2))
% 0.32/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.32/0.52          | ~ (l2_lattices @ X1)
% 0.32/0.52          | (v2_struct_0 @ X1))),
% 0.32/0.52      inference('cnf', [status(esa)], [d17_lattices])).
% 0.32/0.52  thf('19', plain,
% 0.32/0.52      (![X1 : $i, X3 : $i]:
% 0.32/0.52         ((v2_struct_0 @ X1)
% 0.32/0.52          | ~ (l2_lattices @ X1)
% 0.32/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.32/0.52          | ((k1_lattices @ X1 @ X3 @ (k6_lattices @ X1)) = (k6_lattices @ X1))
% 0.32/0.52          | ~ (m1_subset_1 @ (k6_lattices @ X1) @ (u1_struct_0 @ X1))
% 0.32/0.52          | ~ (v14_lattices @ X1))),
% 0.32/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.32/0.52  thf('20', plain,
% 0.32/0.52      (![X0 : $i, X1 : $i]:
% 0.32/0.52         ((v2_struct_0 @ X0)
% 0.32/0.52          | ~ (l2_lattices @ X0)
% 0.32/0.52          | ~ (v14_lattices @ X0)
% 0.32/0.52          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 0.32/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.32/0.52          | ~ (l2_lattices @ X0)
% 0.32/0.52          | (v2_struct_0 @ X0))),
% 0.32/0.52      inference('sup-', [status(thm)], ['17', '19'])).
% 0.32/0.52  thf('21', plain,
% 0.32/0.52      (![X0 : $i, X1 : $i]:
% 0.32/0.52         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.32/0.52          | ((k1_lattices @ X0 @ X1 @ (k6_lattices @ X0)) = (k6_lattices @ X0))
% 0.32/0.52          | ~ (v14_lattices @ X0)
% 0.32/0.52          | ~ (l2_lattices @ X0)
% 0.32/0.52          | (v2_struct_0 @ X0))),
% 0.32/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.32/0.52  thf('22', plain,
% 0.32/0.52      (((v2_struct_0 @ sk_A)
% 0.32/0.52        | ~ (l2_lattices @ sk_A)
% 0.32/0.52        | ~ (v14_lattices @ sk_A)
% 0.32/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52            = (k6_lattices @ sk_A)))),
% 0.32/0.52      inference('sup-', [status(thm)], ['16', '21'])).
% 0.32/0.52  thf('23', plain, ((l2_lattices @ sk_A)),
% 0.32/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.32/0.52  thf('24', plain, ((v14_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('25', plain,
% 0.32/0.52      (((v2_struct_0 @ sk_A)
% 0.32/0.52        | ((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52            = (k6_lattices @ sk_A)))),
% 0.32/0.52      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.32/0.52  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('27', plain,
% 0.32/0.52      (((k1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52         = (k6_lattices @ sk_A))),
% 0.32/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.32/0.52  thf('28', plain,
% 0.32/0.52      ((((k6_lattices @ sk_A) != (k6_lattices @ sk_A))
% 0.32/0.52        | (r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.32/0.52      inference('demod', [status(thm)], ['15', '27'])).
% 0.32/0.52  thf('29', plain, ((r1_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))),
% 0.32/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.32/0.52  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf(redefinition_r3_lattices, axiom,
% 0.32/0.52    (![A:$i,B:$i,C:$i]:
% 0.32/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.32/0.52         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.32/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.32/0.52         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.32/0.52       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.32/0.52  thf('31', plain,
% 0.32/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.32/0.52         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.32/0.52          | ~ (l3_lattices @ X10)
% 0.32/0.52          | ~ (v9_lattices @ X10)
% 0.32/0.52          | ~ (v8_lattices @ X10)
% 0.32/0.52          | ~ (v6_lattices @ X10)
% 0.32/0.52          | (v2_struct_0 @ X10)
% 0.32/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.32/0.52          | (r3_lattices @ X10 @ X9 @ X11)
% 0.32/0.52          | ~ (r1_lattices @ X10 @ X9 @ X11))),
% 0.32/0.52      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.32/0.52  thf('32', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.32/0.52          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.32/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.32/0.52          | (v2_struct_0 @ sk_A)
% 0.32/0.52          | ~ (v6_lattices @ sk_A)
% 0.32/0.52          | ~ (v8_lattices @ sk_A)
% 0.32/0.52          | ~ (v9_lattices @ sk_A)
% 0.32/0.52          | ~ (l3_lattices @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.32/0.52  thf(cc1_lattices, axiom,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( l3_lattices @ A ) =>
% 0.32/0.52       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.32/0.52         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.32/0.52           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.32/0.52           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.32/0.52  thf('33', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         ((v2_struct_0 @ X0)
% 0.32/0.52          | ~ (v10_lattices @ X0)
% 0.32/0.52          | (v6_lattices @ X0)
% 0.32/0.52          | ~ (l3_lattices @ X0))),
% 0.32/0.52      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.32/0.52  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('35', plain,
% 0.32/0.52      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.32/0.52  thf('36', plain, ((l3_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('37', plain, ((v10_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('38', plain, ((v6_lattices @ sk_A)),
% 0.32/0.52      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.32/0.52  thf('39', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         ((v2_struct_0 @ X0)
% 0.32/0.52          | ~ (v10_lattices @ X0)
% 0.32/0.52          | (v8_lattices @ X0)
% 0.32/0.52          | ~ (l3_lattices @ X0))),
% 0.32/0.52      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.32/0.52  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('41', plain,
% 0.32/0.52      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.32/0.52  thf('42', plain, ((l3_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('43', plain, ((v10_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('44', plain, ((v8_lattices @ sk_A)),
% 0.32/0.52      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.32/0.52  thf('45', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         ((v2_struct_0 @ X0)
% 0.32/0.52          | ~ (v10_lattices @ X0)
% 0.32/0.52          | (v9_lattices @ X0)
% 0.32/0.52          | ~ (l3_lattices @ X0))),
% 0.32/0.52      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.32/0.52  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('47', plain,
% 0.32/0.52      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.32/0.52  thf('48', plain, ((l3_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('49', plain, ((v10_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('50', plain, ((v9_lattices @ sk_A)),
% 0.32/0.52      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.32/0.52  thf('51', plain, ((l3_lattices @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('52', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (~ (r1_lattices @ sk_A @ sk_B @ X0)
% 0.32/0.52          | (r3_lattices @ sk_A @ sk_B @ X0)
% 0.32/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.32/0.52          | (v2_struct_0 @ sk_A))),
% 0.32/0.52      inference('demod', [status(thm)], ['32', '38', '44', '50', '51'])).
% 0.32/0.52  thf('53', plain,
% 0.32/0.52      (((v2_struct_0 @ sk_A)
% 0.32/0.52        | ~ (m1_subset_1 @ (k6_lattices @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.32/0.52        | (r3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A)))),
% 0.32/0.52      inference('sup-', [status(thm)], ['29', '52'])).
% 0.32/0.52  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('55', plain,
% 0.32/0.52      (((r3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))
% 0.32/0.52        | ~ (m1_subset_1 @ (k6_lattices @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.32/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.32/0.52  thf('56', plain, (~ (r3_lattices @ sk_A @ sk_B @ (k6_lattices @ sk_A))),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('57', plain,
% 0.32/0.52      (~ (m1_subset_1 @ (k6_lattices @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.32/0.52      inference('clc', [status(thm)], ['55', '56'])).
% 0.32/0.52  thf('58', plain, (((v2_struct_0 @ sk_A) | ~ (l2_lattices @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['1', '57'])).
% 0.32/0.52  thf('59', plain, ((l2_lattices @ sk_A)),
% 0.32/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.32/0.52  thf('60', plain, ((v2_struct_0 @ sk_A)),
% 0.32/0.52      inference('demod', [status(thm)], ['58', '59'])).
% 0.32/0.52  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.32/0.52  
% 0.32/0.52  % SZS output end Refutation
% 0.32/0.52  
% 0.32/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
