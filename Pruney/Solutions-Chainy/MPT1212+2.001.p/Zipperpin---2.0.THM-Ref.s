%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8S8nivsW5

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 163 expanded)
%              Number of leaves         :   34 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  641 (1939 expanded)
%              Number of equality atoms :   20 (  76 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r2_lattices_type,type,(
    r2_lattices: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_lattices_type,type,(
    k6_lattices: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v16_lattices_type,type,(
    v16_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(v15_lattices_type,type,(
    v15_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(t48_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B )
            = ( k6_lattices @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B )
              = ( k6_lattices @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_lattices])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d21_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ~ ( v2_struct_0 @ A )
              & ( v10_lattices @ A )
              & ( v11_lattices @ A )
              & ( v16_lattices @ A )
              & ( l3_lattices @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( C
                    = ( k7_lattices @ A @ B ) )
                <=> ( r2_lattices @ A @ C @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ( X7
       != ( k7_lattices @ X6 @ X5 ) )
      | ( r2_lattices @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v16_lattices @ X6 )
      | ~ ( v11_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d21_lattices])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( v11_lattices @ X6 )
      | ~ ( v16_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ~ ( m1_subset_1 @ ( k7_lattices @ X6 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ( r2_lattices @ X6 @ ( k7_lattices @ X6 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v16_lattices @ sk_A )
    | ~ ( v11_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v17_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v11_lattices @ A )
          & ( v15_lattices @ A )
          & ( v16_lattices @ A ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v17_lattices @ X1 )
      | ( v16_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v16_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v16_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v17_lattices @ X1 )
      | ( v11_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc5_lattices])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v11_lattices @ sk_A )
    | ~ ( v17_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v11_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12','18','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d18_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_lattices @ A @ B @ C )
              <=> ( ( ( k1_lattices @ A @ B @ C )
                    = ( k6_lattices @ A ) )
                  & ( ( k1_lattices @ A @ C @ B )
                    = ( k6_lattices @ A ) )
                  & ( ( k2_lattices @ A @ B @ C )
                    = ( k5_lattices @ A ) )
                  & ( ( k2_lattices @ A @ C @ B )
                    = ( k5_lattices @ A ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_lattices @ X3 @ X2 @ X4 )
      | ( ( k1_lattices @ X3 @ X2 @ X4 )
        = ( k6_lattices @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_lattices])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k6_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k6_lattices @ sk_A ) )
      | ~ ( r2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
      = ( k6_lattices @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l2_lattices @ X12 )
      | ~ ( v4_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( ( k3_lattices @ X12 @ X11 @ X13 )
        = ( k1_lattices @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('46',plain,(
    ! [X10: $i] :
      ( ( l2_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('47',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','44','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
      = ( k6_lattices @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','51','52'])).

thf('54',plain,(
    ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ sk_B )
 != ( k6_lattices @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C8S8nivsW5
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.57  % Solved by: fo/fo7.sh
% 0.19/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.57  % done 127 iterations in 0.122s
% 0.19/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.57  % SZS output start Refutation
% 0.19/0.57  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.19/0.57  thf(r2_lattices_type, type, r2_lattices: $i > $i > $i > $o).
% 0.19/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.57  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.19/0.57  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.19/0.57  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.19/0.57  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.19/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.57  thf(k6_lattices_type, type, k6_lattices: $i > $i).
% 0.19/0.57  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.19/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.57  thf(v16_lattices_type, type, v16_lattices: $i > $o).
% 0.19/0.57  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.19/0.57  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.19/0.57  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 0.19/0.57  thf(v15_lattices_type, type, v15_lattices: $i > $o).
% 0.19/0.57  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.19/0.57  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 0.19/0.57  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.19/0.57  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.19/0.57  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.19/0.57  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 0.19/0.57  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.19/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.57  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.19/0.57  thf(t48_lattices, conjecture,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.57         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.57           ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B ) =
% 0.19/0.57             ( k6_lattices @ A ) ) ) ) ))).
% 0.19/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.57    (~( ![A:$i]:
% 0.19/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.57            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.19/0.57          ( ![B:$i]:
% 0.19/0.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.57              ( ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ B ) =
% 0.19/0.57                ( k6_lattices @ A ) ) ) ) ) )),
% 0.19/0.57    inference('cnf.neg', [status(esa)], [t48_lattices])).
% 0.19/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(dt_k7_lattices, axiom,
% 0.19/0.57    (![A:$i,B:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.19/0.57         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.57       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.19/0.57  thf('2', plain,
% 0.19/0.57      (![X8 : $i, X9 : $i]:
% 0.19/0.57         (~ (l3_lattices @ X8)
% 0.19/0.57          | (v2_struct_0 @ X8)
% 0.19/0.57          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.19/0.57          | (m1_subset_1 @ (k7_lattices @ X8 @ X9) @ (u1_struct_0 @ X8)))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.19/0.57  thf('3', plain,
% 0.19/0.57      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.57        | (v2_struct_0 @ sk_A)
% 0.19/0.57        | ~ (l3_lattices @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.57  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('5', plain,
% 0.19/0.57      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.57        | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.57  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('7', plain,
% 0.19/0.57      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.57      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.57  thf(d21_lattices, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.57           ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.19/0.57               ( v11_lattices @ A ) & ( v16_lattices @ A ) & 
% 0.19/0.57               ( l3_lattices @ A ) ) =>
% 0.19/0.57             ( ![C:$i]:
% 0.19/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.57                 ( ( ( C ) = ( k7_lattices @ A @ B ) ) <=>
% 0.19/0.57                   ( r2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.19/0.57  thf('8', plain,
% 0.19/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6))
% 0.19/0.57          | ((X7) != (k7_lattices @ X6 @ X5))
% 0.19/0.57          | (r2_lattices @ X6 @ X7 @ X5)
% 0.19/0.57          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.19/0.57          | ~ (l3_lattices @ X6)
% 0.19/0.57          | ~ (v16_lattices @ X6)
% 0.19/0.57          | ~ (v11_lattices @ X6)
% 0.19/0.57          | ~ (v10_lattices @ X6)
% 0.19/0.57          | (v2_struct_0 @ X6)
% 0.19/0.57          | ~ (l3_lattices @ X6)
% 0.19/0.57          | (v2_struct_0 @ X6))),
% 0.19/0.57      inference('cnf', [status(esa)], [d21_lattices])).
% 0.19/0.57  thf('9', plain,
% 0.19/0.57      (![X5 : $i, X6 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X6)
% 0.19/0.57          | ~ (v10_lattices @ X6)
% 0.19/0.57          | ~ (v11_lattices @ X6)
% 0.19/0.57          | ~ (v16_lattices @ X6)
% 0.19/0.57          | ~ (l3_lattices @ X6)
% 0.19/0.57          | ~ (m1_subset_1 @ (k7_lattices @ X6 @ X5) @ (u1_struct_0 @ X6))
% 0.19/0.57          | (r2_lattices @ X6 @ (k7_lattices @ X6 @ X5) @ X5)
% 0.19/0.57          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X6)))),
% 0.19/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.57  thf('10', plain,
% 0.19/0.57      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.57        | (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.19/0.57        | ~ (l3_lattices @ sk_A)
% 0.19/0.57        | ~ (v16_lattices @ sk_A)
% 0.19/0.57        | ~ (v11_lattices @ sk_A)
% 0.19/0.57        | ~ (v10_lattices @ sk_A)
% 0.19/0.57        | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['7', '9'])).
% 0.19/0.57  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('12', plain, ((l3_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(cc5_lattices, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( l3_lattices @ A ) =>
% 0.19/0.57       ( ( ( ~( v2_struct_0 @ A ) ) & ( v17_lattices @ A ) ) =>
% 0.19/0.57         ( ( ~( v2_struct_0 @ A ) ) & ( v11_lattices @ A ) & 
% 0.19/0.57           ( v15_lattices @ A ) & ( v16_lattices @ A ) ) ) ))).
% 0.19/0.57  thf('13', plain,
% 0.19/0.57      (![X1 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X1)
% 0.19/0.57          | ~ (v17_lattices @ X1)
% 0.19/0.57          | (v16_lattices @ X1)
% 0.19/0.57          | ~ (l3_lattices @ X1))),
% 0.19/0.57      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.19/0.57  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('15', plain,
% 0.19/0.57      ((~ (l3_lattices @ sk_A)
% 0.19/0.57        | (v16_lattices @ sk_A)
% 0.19/0.57        | ~ (v17_lattices @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.57  thf('16', plain, ((l3_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('17', plain, ((v17_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('18', plain, ((v16_lattices @ sk_A)),
% 0.19/0.57      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.19/0.57  thf('19', plain,
% 0.19/0.57      (![X1 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X1)
% 0.19/0.57          | ~ (v17_lattices @ X1)
% 0.19/0.57          | (v11_lattices @ X1)
% 0.19/0.57          | ~ (l3_lattices @ X1))),
% 0.19/0.57      inference('cnf', [status(esa)], [cc5_lattices])).
% 0.19/0.57  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('21', plain,
% 0.19/0.57      ((~ (l3_lattices @ sk_A)
% 0.19/0.57        | (v11_lattices @ sk_A)
% 0.19/0.57        | ~ (v17_lattices @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.57  thf('22', plain, ((l3_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('23', plain, ((v17_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('24', plain, ((v11_lattices @ sk_A)),
% 0.19/0.57      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.19/0.57  thf('25', plain, ((v10_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('26', plain,
% 0.19/0.57      (((r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.19/0.57        | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['10', '11', '12', '18', '24', '25'])).
% 0.19/0.57  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('28', plain, ((r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)),
% 0.19/0.57      inference('clc', [status(thm)], ['26', '27'])).
% 0.19/0.57  thf('29', plain,
% 0.19/0.57      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.57      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.57  thf(d18_lattices, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.57           ( ![C:$i]:
% 0.19/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.57               ( ( r2_lattices @ A @ B @ C ) <=>
% 0.19/0.57                 ( ( ( k1_lattices @ A @ B @ C ) = ( k6_lattices @ A ) ) & 
% 0.19/0.57                   ( ( k1_lattices @ A @ C @ B ) = ( k6_lattices @ A ) ) & 
% 0.19/0.57                   ( ( k2_lattices @ A @ B @ C ) = ( k5_lattices @ A ) ) & 
% 0.19/0.57                   ( ( k2_lattices @ A @ C @ B ) = ( k5_lattices @ A ) ) ) ) ) ) ) ) ))).
% 0.19/0.57  thf('30', plain,
% 0.19/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.19/0.57          | ~ (r2_lattices @ X3 @ X2 @ X4)
% 0.19/0.57          | ((k1_lattices @ X3 @ X2 @ X4) = (k6_lattices @ X3))
% 0.19/0.57          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.19/0.57          | ~ (l3_lattices @ X3)
% 0.19/0.57          | (v2_struct_0 @ X3))),
% 0.19/0.57      inference('cnf', [status(esa)], [d18_lattices])).
% 0.19/0.57  thf('31', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((v2_struct_0 @ sk_A)
% 0.19/0.57          | ~ (l3_lattices @ sk_A)
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.57          | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.19/0.57              = (k6_lattices @ sk_A))
% 0.19/0.57          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.19/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.57  thf('32', plain, ((l3_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('33', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((v2_struct_0 @ sk_A)
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.57          | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.19/0.57              = (k6_lattices @ sk_A))
% 0.19/0.57          | ~ (r2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))),
% 0.19/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.57  thf('34', plain,
% 0.19/0.57      ((((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.19/0.57          = (k6_lattices @ sk_A))
% 0.19/0.57        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.57        | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['28', '33'])).
% 0.19/0.57  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('36', plain,
% 0.19/0.57      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.57      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.57  thf(redefinition_k3_lattices, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.19/0.57         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.57         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.57       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.19/0.57  thf('37', plain,
% 0.19/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.19/0.57          | ~ (l2_lattices @ X12)
% 0.19/0.57          | ~ (v4_lattices @ X12)
% 0.19/0.57          | (v2_struct_0 @ X12)
% 0.19/0.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.19/0.57          | ((k3_lattices @ X12 @ X11 @ X13) = (k1_lattices @ X12 @ X11 @ X13)))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.19/0.57  thf('38', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.19/0.57            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.57          | (v2_struct_0 @ sk_A)
% 0.19/0.57          | ~ (v4_lattices @ sk_A)
% 0.19/0.57          | ~ (l2_lattices @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.57  thf(cc1_lattices, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( l3_lattices @ A ) =>
% 0.19/0.57       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.19/0.57         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.19/0.57           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.19/0.57           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.19/0.57  thf('39', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         ((v2_struct_0 @ X0)
% 0.19/0.57          | ~ (v10_lattices @ X0)
% 0.19/0.57          | (v4_lattices @ X0)
% 0.19/0.57          | ~ (l3_lattices @ X0))),
% 0.19/0.57      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.19/0.57  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('41', plain,
% 0.19/0.57      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.19/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.57  thf('42', plain, ((l3_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('43', plain, ((v10_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('44', plain, ((v4_lattices @ sk_A)),
% 0.19/0.57      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.19/0.57  thf('45', plain, ((l3_lattices @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(dt_l3_lattices, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.19/0.57  thf('46', plain,
% 0.19/0.57      (![X10 : $i]: ((l2_lattices @ X10) | ~ (l3_lattices @ X10))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.19/0.57  thf('47', plain, ((l2_lattices @ sk_A)),
% 0.19/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.57  thf('48', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.19/0.57            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.57          | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['38', '44', '47'])).
% 0.19/0.57  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('50', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.57          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.19/0.57              = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)))),
% 0.19/0.57      inference('clc', [status(thm)], ['48', '49'])).
% 0.19/0.57  thf('51', plain,
% 0.19/0.57      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.19/0.57         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B))),
% 0.19/0.57      inference('sup-', [status(thm)], ['35', '50'])).
% 0.19/0.57  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('53', plain,
% 0.19/0.57      ((((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.19/0.57          = (k6_lattices @ sk_A))
% 0.19/0.57        | (v2_struct_0 @ sk_A))),
% 0.19/0.57      inference('demod', [status(thm)], ['34', '51', '52'])).
% 0.19/0.57  thf('54', plain,
% 0.19/0.57      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ sk_B)
% 0.19/0.57         != (k6_lattices @ sk_A))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('55', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.57      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.19/0.57  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.19/0.57  
% 0.19/0.57  % SZS output end Refutation
% 0.19/0.57  
% 0.19/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
