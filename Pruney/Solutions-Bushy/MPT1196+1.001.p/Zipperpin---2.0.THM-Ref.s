%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1196+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z7PIu6RZ6y

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:14 EST 2020

% Result     : Theorem 56.55s
% Output     : Refutation 56.55s
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
