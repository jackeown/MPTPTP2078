%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OHgXEipAbF

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 117 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  591 (1209 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v3_lattices_type,type,(
    v3_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ ( k1_lattice3 @ X17 ) ) )
      | ( ( k1_lattices @ ( k1_lattice3 @ X17 ) @ X18 @ X16 )
        = ( k2_xboole_0 @ X18 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ ( k1_lattice3 @ X17 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_lattices @ X9 @ X8 @ X10 )
      | ( ( k1_lattices @ X9 @ X8 @ X10 )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l2_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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
    ! [X13: $i] :
      ( l3_lattices @ ( k1_lattice3 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_lattice3])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
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
    ! [X14: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X14 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C )
      = sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( ( k1_lattices @ X9 @ X8 @ X10 )
       != X10 )
      | ( r1_lattices @ X9 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l2_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( l2_lattices @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( l2_lattices @ ( k1_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_lattice3 @ sk_A ) ) )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
      | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
     != sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k1_lattice3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X14: $i] :
      ~ ( v2_struct_0 @ ( k1_lattice3 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_lattice3])).

thf('41',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
     != sk_C ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('43',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
    | ( ( k2_xboole_0 @ sk_B @ sk_C )
     != sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,
    ( ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C )
   <= ~ ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_lattices @ ( k1_lattice3 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OHgXEipAbF
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 173 iterations in 0.077s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.20/0.52  thf(v3_lattices_type, type, v3_lattices: $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.20/0.52  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.20/0.52  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(t2_lattice3, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.20/0.52           ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) <=>
% 0.20/0.52             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.20/0.52              ( ( r1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) <=>
% 0.20/0.52                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t2_lattice3])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.20/0.52        | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.20/0.52       ~ ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t1_lattice3, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k1_lattice3 @ A ) ) ) =>
% 0.20/0.52           ( ( ( k1_lattices @ ( k1_lattice3 @ A ) @ B @ C ) =
% 0.20/0.52               ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.52             ( ( k2_lattices @ ( k1_lattice3 @ A ) @ B @ C ) =
% 0.20/0.52               ( k3_xboole_0 @ B @ C ) ) ) ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ (k1_lattice3 @ X17)))
% 0.20/0.52          | ((k1_lattices @ (k1_lattice3 @ X17) @ X18 @ X16)
% 0.20/0.52              = (k2_xboole_0 @ X18 @ X16))
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ (k1_lattice3 @ X17))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_lattice3])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.20/0.52          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ X0 @ sk_C)
% 0.20/0.52              = (k2_xboole_0 @ X0 @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ sk_C)
% 0.20/0.52        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.52         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_lattices, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.20/0.53                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ~ (r1_lattices @ X9 @ X8 @ X10)
% 0.20/0.53          | ((k1_lattices @ X9 @ X8 @ X10) = (X10))
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ~ (l2_lattices @ X9)
% 0.20/0.53          | (v2_struct_0 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_lattices])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.20/0.53          | ~ (l2_lattices @ (k1_lattice3 @ sk_A))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.20/0.53          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) = (X0))
% 0.20/0.53          | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf(dt_k1_lattice3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.53       ( v3_lattices @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.53  thf('13', plain, (![X13 : $i]: (l3_lattices @ (k1_lattice3 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_lattice3])).
% 0.20/0.53  thf(dt_l3_lattices, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X11 : $i]: ((l2_lattices @ X11) | ~ (l3_lattices @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.20/0.53  thf('15', plain, (![X0 : $i]: (l2_lattices @ (k1_lattice3 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.20/0.53          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) = (X0))
% 0.20/0.53          | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.53        | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) = (sk_C))
% 0.20/0.53        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.53  thf(fc1_lattice3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v3_lattices @ ( k1_lattice3 @ A ) ) & 
% 0.20/0.53       ( ~( v2_struct_0 @ ( k1_lattice3 @ A ) ) ) ))).
% 0.20/0.53  thf('18', plain, (![X14 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) = (sk_C))
% 0.20/0.53        | ~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) = (sk_C)))
% 0.20/0.53         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((((k2_xboole_0 @ sk_B @ sk_C) = (sk_C)))
% 0.20/0.53         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['6', '20'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf(t11_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ sk_C))
% 0.20/0.53         <= (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['21', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.20/0.53       ~ ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ sk_C)) | 
% 0.20/0.53       ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.53      inference('split', [status(esa)], ['7'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['7'])).
% 0.20/0.53  thf(t12_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((k2_xboole_0 @ sk_B @ sk_C) = (sk_C)))
% 0.20/0.53         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ((k1_lattices @ X9 @ X8 @ X10) != (X10))
% 0.20/0.53          | (r1_lattices @ X9 @ X8 @ X10)
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ~ (l2_lattices @ X9)
% 0.20/0.53          | (v2_struct_0 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_lattices])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.20/0.53          | ~ (l2_lattices @ (k1_lattice3 @ sk_A))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.20/0.53          | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.20/0.53          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) != (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain, (![X0 : $i]: (l2_lattices @ (k1_lattice3 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ (k1_lattice3 @ sk_A))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_lattice3 @ sk_A)))
% 0.20/0.53          | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0)
% 0.20/0.53          | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ X0) != (X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) != (sk_C))
% 0.20/0.53        | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.53        | (v2_struct_0 @ (k1_lattice3 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '38'])).
% 0.20/0.53  thf('40', plain, (![X14 : $i]: ~ (v2_struct_0 @ (k1_lattice3 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_lattice3])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.53        | ((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C) != (sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((k1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.53         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.53        | ((k2_xboole_0 @ sk_B @ sk_C) != (sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((((sk_C) != (sk_C))
% 0.20/0.53         | (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.53         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((~ (r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.53         <= (~ ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 0.20/0.53       ((r1_lattices @ (k1_lattice3 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '28', '29', '47'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
