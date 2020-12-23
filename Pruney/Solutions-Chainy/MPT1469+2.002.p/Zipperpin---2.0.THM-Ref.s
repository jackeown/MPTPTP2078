%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mzJ61TmvIY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 113 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  562 (1180 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(t2_lattice3,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
         => ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
           => ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_lattice3])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) )
         => ( ( ( k1_lattices @ ( k1_lattice3 @ A ) @ B @ C )
              = ( k2_xboole_0 @ B @ C ) )
            & ( ( k2_lattices @ ( k1_lattice3 @ A ) @ B @ C )
              = ( k3_xboole_0 @ B @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ ( k1_lattice3 @ X13 ) ) )
      | ( ( k1_lattices @ ( k1_lattice3 @ X13 ) @ X14 @ X12 )
        = ( k2_xboole_0 @ X14 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ ( k1_lattice3 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[t1_lattice3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ X0 @ sk_C )
        = ( k2_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
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

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_lattices @ X5 @ X4 @ X6 )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l2_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(dt_k1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ ( k1_lattice3 @ A ) )
      & ( v3_lattices @ ( k1_lattice3 @ A ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( l2_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('15',plain,(
    ! [X0: $i] :
      ( l2_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
        = X0 )
      | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
      = sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(fc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( v3_lattices @ ( k1_lattice3 @ A ) )
      & ~ ( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('19',plain,
    ( ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
      = sk_C )
    | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
      = sk_C )
   <= ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C )
      = sk_C )
   <= ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['6','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C )
      = sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
       != X6 )
      | ( r1_lattices @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l2_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( l2_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
     != sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X10: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('38',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
     != sk_C ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('40',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( ( k2_xboole_0 @ sk_B @ sk_C )
     != sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','25','26','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mzJ61TmvIY
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 63 iterations in 0.030s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.22/0.49  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.22/0.49  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.22/0.49  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.22/0.49  thf(t2_lattice3, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.22/0.49           ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) <=>
% 0.22/0.49             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.22/0.49          ( ![C:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.22/0.49              ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) <=>
% 0.22/0.49                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t2_lattice3])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.22/0.49        | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.22/0.49       ~ ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t1_lattice3, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.22/0.49           ( ( ( k1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) =
% 0.22/0.49               ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.49             ( ( k2_lattices @ ( k1_lattice3 @ A ) @ B @ C ) =
% 0.22/0.49               ( k3_xboole_0 @ B @ C ) ) ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ (k1_lattice3 @ X13)))
% 0.22/0.49          | ((k1_lattices @ (k1_lattice3 @ X13) @ X14 @ X12)
% 0.22/0.49              = (k2_xboole_0 @ X14 @ X12))
% 0.22/0.49          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ (k1_lattice3 @ X13))))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_lattice3])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.22/0.49          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ X0 @ sk_C)
% 0.22/0.49              = (k2_xboole_0 @ X0 @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.49         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)
% 0.22/0.49        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.22/0.49         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_lattices, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.22/0.49                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (r1_lattices @ X5 @ X4 @ X6)
% 0.22/0.49          | ((k1_lattices @ X5 @ X4 @ X6) = (X6))
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (l2_lattices @ X5)
% 0.22/0.49          | (v2_struct_0 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_lattices])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.22/0.49          | ~ (l2_lattices @ (k1_lattice3 @ sk_A))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.22/0.49          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) = (X0))
% 0.22/0.49          | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf(dt_k1_lattice3, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.22/0.49       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.22/0.49  thf('13', plain, (![X9 : $i]: (l3_lattices @ (k1_lattice3 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.22/0.49  thf(dt_l3_lattices, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.22/0.49  thf('14', plain, (![X7 : $i]: ((l2_lattices @ X7) | ~ (l3_lattices @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.22/0.49  thf('15', plain, (![X0 : $i]: (l2_lattices @ (k1_lattice3 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.22/0.49          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) = (X0))
% 0.22/0.49          | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['12', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.49        | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) = (sk_C))
% 0.22/0.49        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.49  thf(fc1_lattice3, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.22/0.49       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.22/0.49  thf('18', plain, (![X10 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) = (sk_C))
% 0.22/0.49        | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.22/0.49      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) = (sk_C)))
% 0.22/0.49         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((((k2_xboole_0 @ sk_B @ sk_C) = (sk_C)))
% 0.22/0.49         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['6', '20'])).
% 0.22/0.49  thf(t7_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C))
% 0.22/0.49         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.22/0.49       ~ ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.22/0.49       ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['7'])).
% 0.22/0.49  thf(t12_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((((k2_xboole_0 @ sk_B @ sk_C) = (sk_C)))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ((k1_lattices @ X5 @ X4 @ X6) != (X6))
% 0.22/0.49          | (r1_lattices @ X5 @ X4 @ X6)
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (l2_lattices @ X5)
% 0.22/0.49          | (v2_struct_0 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_lattices])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.22/0.49          | ~ (l2_lattices @ (k1_lattice3 @ sk_A))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.22/0.49          | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.22/0.49          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) != (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain, (![X0 : $i]: (l2_lattices @ (k1_lattice3 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.22/0.49          | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.22/0.49          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) != (X0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) != (sk_C))
% 0.22/0.49        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.49        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '35'])).
% 0.22/0.49  thf('37', plain, (![X10 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.49        | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) != (sk_C)))),
% 0.22/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.49         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.49        | ((k2_xboole_0 @ sk_B @ sk_C) != (sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (((((sk_C) != (sk_C))
% 0.22/0.49         | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.22/0.49         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      ((~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.22/0.49         <= (~ ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.22/0.49       ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.49  thf('45', plain, ($false),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['1', '25', '26', '44'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
