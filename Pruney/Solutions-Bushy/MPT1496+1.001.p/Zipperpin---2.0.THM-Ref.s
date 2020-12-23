%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1496+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sxsJb4o7m

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 270 expanded)
%              Number of leaves         :   18 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  561 (3701 expanded)
%              Number of equality atoms :   13 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_lattice3_type,type,(
    k5_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_lattice3_type,type,(
    k4_lattice3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t29_lattice3,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( l3_lattices @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_lattice3 @ B ) ) )
         => ( ( r1_lattice3 @ ( k3_lattice3 @ B ) @ A @ C )
          <=> ( r3_lattice3 @ B @ ( k5_lattice3 @ B @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ~ ( v2_struct_0 @ B )
          & ( v10_lattices @ B )
          & ( l3_lattices @ B ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k3_lattice3 @ B ) ) )
           => ( ( r1_lattice3 @ ( k3_lattice3 @ B ) @ A @ C )
            <=> ( r3_lattice3 @ B @ ( k5_lattice3 @ B @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_lattice3])).

thf('0',plain,
    ( ~ ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
    | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
    | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l3_lattices @ X4 )
      | ~ ( v10_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ ( k3_lattice3 @ X4 ) ) )
      | ( m1_subset_1 @ ( k5_lattice3 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattice3])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k5_lattice3 @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k3_lattice3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k3_lattice3 @ A ) ) )
         => ( ( k5_lattice3 @ A @ B )
            = B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k3_lattice3 @ X3 ) ) )
      | ( ( k5_lattice3 @ X3 @ X2 )
        = X2 )
      | ~ ( l3_lattices @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_lattice3])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( ( k5_lattice3 @ sk_B @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k5_lattice3 @ sk_B @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k5_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d3_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattice3 @ A @ B )
            = B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k4_lattice3 @ X1 @ X0 )
        = X0 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattice3])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v10_lattices @ sk_B )
    | ~ ( l3_lattices @ sk_B )
    | ( ( k4_lattice3 @ sk_B @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k4_lattice3 @ sk_B @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['24','25'])).

thf(t28_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( l3_lattices @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
         => ( ( r3_lattice3 @ B @ C @ A )
          <=> ( r1_lattice3 @ ( k3_lattice3 @ B ) @ A @ ( k4_lattice3 @ B @ C ) ) ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_lattice3 @ ( k3_lattice3 @ X7 ) @ X8 @ ( k4_lattice3 @ X7 @ X6 ) )
      | ( r3_lattice3 @ X7 @ X6 @ X8 )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_lattice3])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
   <= ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','34'])).

thf('36',plain,
    ( ( k5_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('37',plain,
    ( ~ ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
   <= ~ ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ~ ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
   <= ~ ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
    | ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,
    ( ( k5_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('42',plain,
    ( ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
   <= ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( r3_lattice3 @ sk_B @ sk_C @ sk_A )
   <= ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r3_lattice3 @ X7 @ X6 @ X8 )
      | ( r1_lattice3 @ ( k3_lattice3 @ X7 ) @ X8 @ ( k4_lattice3 @ X7 @ X6 ) )
      | ~ ( l3_lattices @ X7 )
      | ~ ( v10_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_lattice3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v10_lattices @ sk_B )
      | ~ ( l3_lattices @ sk_B )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ ( k4_lattice3 @ sk_B @ sk_C ) )
      | ~ ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v10_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l3_lattices @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k4_lattice3 @ sk_B @ sk_C )
    = sk_C ),
    inference(clc,[status(thm)],['24','25'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C )
      | ~ ( r3_lattice3 @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattice3 @ sk_B @ sk_C @ X0 )
      | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
   <= ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,
    ( ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C )
   <= ~ ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ~ ( r3_lattice3 @ sk_B @ ( k5_lattice3 @ sk_B @ sk_C ) @ sk_A )
    | ( r1_lattice3 @ ( k3_lattice3 @ sk_B ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','55'])).


%------------------------------------------------------------------------------
