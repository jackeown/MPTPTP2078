%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yi3YsYRdGG

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:30 EST 2020

% Result     : Theorem 55.33s
% Output     : Refutation 55.33s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  690 (1728 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( l2_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ( ( v5_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( k1_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) )
                      = ( k1_lattices @ A @ ( k1_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( v5_lattices @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( ( k1_lattices @ X3 @ X5 @ ( k1_lattices @ X3 @ X4 @ X6 ) )
        = ( k1_lattices @ X3 @ ( k1_lattices @ X3 @ X5 @ X4 ) @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l2_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_lattices])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_1 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X0 @ sk_B_1 ) @ X1 ) )
      | ~ ( v5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v5_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_1 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X0 @ sk_B_1 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( ( k1_lattices @ sk_A @ X1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_lattices @ sk_A @ X1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k1_lattices @ A @ B @ B )
            = B ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( ( k1_lattices @ X12 @ X11 @ X11 )
        = X11 )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v9_lattices @ X12 )
      | ~ ( v8_lattices @ X12 )
      | ~ ( v6_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t17_lattices])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_B_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( l2_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l2_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k1_lattices @ X8 @ X7 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattices])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X10: $i] :
      ( ( l2_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
       != X2 )
      | ( r1_lattices @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ sk_A )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
       != X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
       != X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
     != ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
     != ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( r1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) )
 != ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yi3YsYRdGG
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 10:07:27 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 55.33/55.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 55.33/55.54  % Solved by: fo/fo7.sh
% 55.33/55.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 55.33/55.54  % done 4874 iterations in 55.052s
% 55.33/55.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 55.33/55.54  % SZS output start Refutation
% 55.33/55.54  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 55.33/55.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 55.33/55.54  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 55.33/55.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 55.33/55.54  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 55.33/55.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 55.33/55.54  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 55.33/55.54  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 55.33/55.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 55.33/55.54  thf(sk_A_type, type, sk_A: $i).
% 55.33/55.54  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 55.33/55.54  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 55.33/55.54  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 55.33/55.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 55.33/55.54  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 55.33/55.54  thf(t22_lattices, conjecture,
% 55.33/55.54    (![A:$i]:
% 55.33/55.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_lattices @ A ) & 
% 55.33/55.54         ( v6_lattices @ A ) & ( v8_lattices @ A ) & ( v9_lattices @ A ) & 
% 55.33/55.54         ( l3_lattices @ A ) ) =>
% 55.33/55.54       ( ![B:$i]:
% 55.33/55.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54           ( ![C:$i]:
% 55.33/55.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54               ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ) ))).
% 55.33/55.54  thf(zf_stmt_0, negated_conjecture,
% 55.33/55.54    (~( ![A:$i]:
% 55.33/55.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_lattices @ A ) & 
% 55.33/55.54            ( v6_lattices @ A ) & ( v8_lattices @ A ) & ( v9_lattices @ A ) & 
% 55.33/55.54            ( l3_lattices @ A ) ) =>
% 55.33/55.54          ( ![B:$i]:
% 55.33/55.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54              ( ![C:$i]:
% 55.33/55.54                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54                  ( r1_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) ) ) ) ) ) )),
% 55.33/55.54    inference('cnf.neg', [status(esa)], [t22_lattices])).
% 55.33/55.54  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf(dt_l3_lattices, axiom,
% 55.33/55.54    (![A:$i]:
% 55.33/55.54     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 55.33/55.54  thf('2', plain, (![X10 : $i]: ((l2_lattices @ X10) | ~ (l3_lattices @ X10))),
% 55.33/55.54      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 55.33/55.54  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf(d5_lattices, axiom,
% 55.33/55.54    (![A:$i]:
% 55.33/55.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 55.33/55.54       ( ( v5_lattices @ A ) <=>
% 55.33/55.54         ( ![B:$i]:
% 55.33/55.54           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54             ( ![C:$i]:
% 55.33/55.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54                 ( ![D:$i]:
% 55.33/55.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54                     ( ( k1_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) ) =
% 55.33/55.54                       ( k1_lattices @ A @ ( k1_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 55.33/55.54  thf('4', plain,
% 55.33/55.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 55.33/55.54         (~ (v5_lattices @ X3)
% 55.33/55.54          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 55.33/55.54          | ((k1_lattices @ X3 @ X5 @ (k1_lattices @ X3 @ X4 @ X6))
% 55.33/55.54              = (k1_lattices @ X3 @ (k1_lattices @ X3 @ X5 @ X4) @ X6))
% 55.33/55.54          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X3))
% 55.33/55.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 55.33/55.54          | ~ (l2_lattices @ X3)
% 55.33/55.54          | (v2_struct_0 @ X3))),
% 55.33/55.54      inference('cnf', [status(esa)], [d5_lattices])).
% 55.33/55.54  thf('5', plain,
% 55.33/55.54      (![X0 : $i, X1 : $i]:
% 55.33/55.54         ((v2_struct_0 @ sk_A)
% 55.33/55.54          | ~ (l2_lattices @ sk_A)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | ((k1_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_1 @ X1))
% 55.33/55.54              = (k1_lattices @ sk_A @ (k1_lattices @ sk_A @ X0 @ sk_B_1) @ X1))
% 55.33/55.54          | ~ (v5_lattices @ sk_A))),
% 55.33/55.54      inference('sup-', [status(thm)], ['3', '4'])).
% 55.33/55.54  thf('6', plain, ((v5_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('7', plain,
% 55.33/55.54      (![X0 : $i, X1 : $i]:
% 55.33/55.54         ((v2_struct_0 @ sk_A)
% 55.33/55.54          | ~ (l2_lattices @ sk_A)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | ((k1_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_1 @ X1))
% 55.33/55.54              = (k1_lattices @ sk_A @ (k1_lattices @ sk_A @ X0 @ sk_B_1) @ X1)))),
% 55.33/55.54      inference('demod', [status(thm)], ['5', '6'])).
% 55.33/55.54  thf('8', plain,
% 55.33/55.54      (![X0 : $i, X1 : $i]:
% 55.33/55.54         (~ (l3_lattices @ sk_A)
% 55.33/55.54          | ((k1_lattices @ sk_A @ X1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 55.33/55.54              = (k1_lattices @ sk_A @ (k1_lattices @ sk_A @ X1 @ sk_B_1) @ X0))
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (v2_struct_0 @ sk_A))),
% 55.33/55.54      inference('sup-', [status(thm)], ['2', '7'])).
% 55.33/55.54  thf('9', plain, ((l3_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('10', plain,
% 55.33/55.54      (![X0 : $i, X1 : $i]:
% 55.33/55.54         (((k1_lattices @ sk_A @ X1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 55.33/55.54            = (k1_lattices @ sk_A @ (k1_lattices @ sk_A @ X1 @ sk_B_1) @ X0))
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (v2_struct_0 @ sk_A))),
% 55.33/55.54      inference('demod', [status(thm)], ['8', '9'])).
% 55.33/55.54  thf('11', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         ((v2_struct_0 @ sk_A)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | ((k1_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54              = (k1_lattices @ sk_A @ (k1_lattices @ sk_A @ X0 @ sk_B_1) @ 
% 55.33/55.54                 sk_C_1)))),
% 55.33/55.54      inference('sup-', [status(thm)], ['1', '10'])).
% 55.33/55.54  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('13', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         (((k1_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54            = (k1_lattices @ sk_A @ (k1_lattices @ sk_A @ X0 @ sk_B_1) @ sk_C_1))
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 55.33/55.54      inference('clc', [status(thm)], ['11', '12'])).
% 55.33/55.54  thf('14', plain,
% 55.33/55.54      (((k1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54         = (k1_lattices @ sk_A @ (k1_lattices @ sk_A @ sk_B_1 @ sk_B_1) @ 
% 55.33/55.54            sk_C_1))),
% 55.33/55.54      inference('sup-', [status(thm)], ['0', '13'])).
% 55.33/55.54  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf(t17_lattices, axiom,
% 55.33/55.54    (![A:$i]:
% 55.33/55.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 55.33/55.54         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 55.33/55.54       ( ![B:$i]:
% 55.33/55.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54           ( ( k1_lattices @ A @ B @ B ) = ( B ) ) ) ) ))).
% 55.33/55.54  thf('16', plain,
% 55.33/55.54      (![X11 : $i, X12 : $i]:
% 55.33/55.54         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 55.33/55.54          | ((k1_lattices @ X12 @ X11 @ X11) = (X11))
% 55.33/55.54          | ~ (l3_lattices @ X12)
% 55.33/55.54          | ~ (v9_lattices @ X12)
% 55.33/55.54          | ~ (v8_lattices @ X12)
% 55.33/55.54          | ~ (v6_lattices @ X12)
% 55.33/55.54          | (v2_struct_0 @ X12))),
% 55.33/55.54      inference('cnf', [status(esa)], [t17_lattices])).
% 55.33/55.54  thf('17', plain,
% 55.33/55.54      (((v2_struct_0 @ sk_A)
% 55.33/55.54        | ~ (v6_lattices @ sk_A)
% 55.33/55.54        | ~ (v8_lattices @ sk_A)
% 55.33/55.54        | ~ (v9_lattices @ sk_A)
% 55.33/55.54        | ~ (l3_lattices @ sk_A)
% 55.33/55.54        | ((k1_lattices @ sk_A @ sk_B_1 @ sk_B_1) = (sk_B_1)))),
% 55.33/55.54      inference('sup-', [status(thm)], ['15', '16'])).
% 55.33/55.54  thf('18', plain, ((v6_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('19', plain, ((v8_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('20', plain, ((v9_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('21', plain, ((l3_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('22', plain,
% 55.33/55.54      (((v2_struct_0 @ sk_A)
% 55.33/55.54        | ((k1_lattices @ sk_A @ sk_B_1 @ sk_B_1) = (sk_B_1)))),
% 55.33/55.54      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 55.33/55.54  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('24', plain, (((k1_lattices @ sk_A @ sk_B_1 @ sk_B_1) = (sk_B_1))),
% 55.33/55.54      inference('clc', [status(thm)], ['22', '23'])).
% 55.33/55.54  thf('25', plain,
% 55.33/55.54      (((k1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54         = (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 55.33/55.54      inference('demod', [status(thm)], ['14', '24'])).
% 55.33/55.54  thf('26', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('27', plain,
% 55.33/55.54      (![X10 : $i]: ((l2_lattices @ X10) | ~ (l3_lattices @ X10))),
% 55.33/55.54      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 55.33/55.54  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf(dt_k1_lattices, axiom,
% 55.33/55.54    (![A:$i,B:$i,C:$i]:
% 55.33/55.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) & 
% 55.33/55.54         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 55.33/55.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 55.33/55.54       ( m1_subset_1 @ ( k1_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 55.33/55.54  thf('29', plain,
% 55.33/55.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 55.33/55.54         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 55.33/55.54          | ~ (l2_lattices @ X8)
% 55.33/55.54          | (v2_struct_0 @ X8)
% 55.33/55.54          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 55.33/55.54          | (m1_subset_1 @ (k1_lattices @ X8 @ X7 @ X9) @ (u1_struct_0 @ X8)))),
% 55.33/55.54      inference('cnf', [status(esa)], [dt_k1_lattices])).
% 55.33/55.54  thf('30', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 55.33/55.54           (u1_struct_0 @ sk_A))
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (v2_struct_0 @ sk_A)
% 55.33/55.54          | ~ (l2_lattices @ sk_A))),
% 55.33/55.54      inference('sup-', [status(thm)], ['28', '29'])).
% 55.33/55.54  thf('31', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         (~ (l3_lattices @ sk_A)
% 55.33/55.54          | (v2_struct_0 @ sk_A)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 55.33/55.54             (u1_struct_0 @ sk_A)))),
% 55.33/55.54      inference('sup-', [status(thm)], ['27', '30'])).
% 55.33/55.54  thf('32', plain, ((l3_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('33', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         ((v2_struct_0 @ sk_A)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 55.33/55.54             (u1_struct_0 @ sk_A)))),
% 55.33/55.54      inference('demod', [status(thm)], ['31', '32'])).
% 55.33/55.54  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('35', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 55.33/55.54           (u1_struct_0 @ sk_A))
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 55.33/55.54      inference('clc', [status(thm)], ['33', '34'])).
% 55.33/55.54  thf('36', plain,
% 55.33/55.54      ((m1_subset_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 55.33/55.54        (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('sup-', [status(thm)], ['26', '35'])).
% 55.33/55.54  thf('37', plain,
% 55.33/55.54      (![X10 : $i]: ((l2_lattices @ X10) | ~ (l3_lattices @ X10))),
% 55.33/55.54      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 55.33/55.54  thf('38', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf(d3_lattices, axiom,
% 55.33/55.54    (![A:$i]:
% 55.33/55.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 55.33/55.54       ( ![B:$i]:
% 55.33/55.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54           ( ![C:$i]:
% 55.33/55.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.33/55.54               ( ( r1_lattices @ A @ B @ C ) <=>
% 55.33/55.54                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 55.33/55.54  thf('39', plain,
% 55.33/55.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.33/55.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 55.33/55.54          | ((k1_lattices @ X1 @ X0 @ X2) != (X2))
% 55.33/55.54          | (r1_lattices @ X1 @ X0 @ X2)
% 55.33/55.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 55.33/55.54          | ~ (l2_lattices @ X1)
% 55.33/55.54          | (v2_struct_0 @ X1))),
% 55.33/55.54      inference('cnf', [status(esa)], [d3_lattices])).
% 55.33/55.54  thf('40', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         ((v2_struct_0 @ sk_A)
% 55.33/55.54          | ~ (l2_lattices @ sk_A)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 55.33/55.54          | ((k1_lattices @ sk_A @ sk_B_1 @ X0) != (X0)))),
% 55.33/55.54      inference('sup-', [status(thm)], ['38', '39'])).
% 55.33/55.54  thf('41', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         (~ (l3_lattices @ sk_A)
% 55.33/55.54          | ((k1_lattices @ sk_A @ sk_B_1 @ X0) != (X0))
% 55.33/55.54          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (v2_struct_0 @ sk_A))),
% 55.33/55.54      inference('sup-', [status(thm)], ['37', '40'])).
% 55.33/55.54  thf('42', plain, ((l3_lattices @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('43', plain,
% 55.33/55.54      (![X0 : $i]:
% 55.33/55.54         (((k1_lattices @ sk_A @ sk_B_1 @ X0) != (X0))
% 55.33/55.54          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 55.33/55.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.33/55.54          | (v2_struct_0 @ sk_A))),
% 55.33/55.54      inference('demod', [status(thm)], ['41', '42'])).
% 55.33/55.54  thf('44', plain,
% 55.33/55.54      (((v2_struct_0 @ sk_A)
% 55.33/55.54        | (r1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54        | ((k1_lattices @ sk_A @ sk_B_1 @ 
% 55.33/55.54            (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54            != (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1)))),
% 55.33/55.54      inference('sup-', [status(thm)], ['36', '43'])).
% 55.33/55.54  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('46', plain,
% 55.33/55.54      ((((k1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54          != (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54        | (r1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1)))),
% 55.33/55.54      inference('clc', [status(thm)], ['44', '45'])).
% 55.33/55.54  thf('47', plain,
% 55.33/55.54      (~ (r1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 55.33/55.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.33/55.54  thf('48', plain,
% 55.33/55.54      (((k1_lattices @ sk_A @ sk_B_1 @ (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))
% 55.33/55.54         != (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 55.33/55.54      inference('clc', [status(thm)], ['46', '47'])).
% 55.33/55.54  thf('49', plain, ($false),
% 55.33/55.54      inference('simplify_reflect-', [status(thm)], ['25', '48'])).
% 55.33/55.54  
% 55.33/55.54  % SZS output end Refutation
% 55.33/55.54  
% 55.33/55.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
