%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IQVIDEmW01

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:31 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 308 expanded)
%              Number of leaves         :   22 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  872 (4337 expanded)
%              Number of equality atoms :   37 (  70 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t23_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v6_lattices @ A )
          & ( v8_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_lattices])).

thf('0',plain,(
    ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k4_lattices @ A @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k4_lattices @ X1 @ X0 @ X2 )
        = ( k4_lattices @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( l1_lattices @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('8',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('25',plain,
    ( ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('38',plain,
    ( ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v8_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k1_lattices @ X6 @ ( k2_lattices @ X6 @ X8 @ X7 ) @ X7 )
        = X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X10 @ X9 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattices])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('61',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

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

thf('62',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ X3 @ X5 )
       != X5 )
      | ( r1_lattices @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( l2_lattices @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('66',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('69',plain,
    ( ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['39','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IQVIDEmW01
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 366 iterations in 0.661s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.91/1.12  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.91/1.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.12  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.12  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.91/1.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.12  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.91/1.12  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.91/1.12  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.12  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.91/1.12  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.91/1.12  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.91/1.12  thf(t23_lattices, conjecture,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.91/1.12         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12           ( ![C:$i]:
% 0.91/1.12             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i]:
% 0.91/1.12        ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.91/1.12            ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.91/1.12          ( ![B:$i]:
% 0.91/1.12            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12              ( ![C:$i]:
% 0.91/1.12                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12                  ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t23_lattices])).
% 0.91/1.12  thf('0', plain,
% 0.91/1.12      (~ (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ sk_B_1)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(commutativity_k4_lattices, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.91/1.12         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.91/1.12         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.91/1.12  thf('3', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.91/1.12          | ~ (l1_lattices @ X1)
% 0.91/1.12          | ~ (v6_lattices @ X1)
% 0.91/1.12          | (v2_struct_0 @ X1)
% 0.91/1.12          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.91/1.12          | ((k4_lattices @ X1 @ X0 @ X2) = (k4_lattices @ X1 @ X2 @ X0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.91/1.12  thf('4', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.91/1.12            = (k4_lattices @ sk_A @ X0 @ sk_B_1))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (v6_lattices @ sk_A)
% 0.91/1.12          | ~ (l1_lattices @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.12  thf('5', plain, ((v6_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('6', plain, ((l3_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(dt_l3_lattices, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.91/1.12  thf('7', plain, (![X12 : $i]: ((l1_lattices @ X12) | ~ (l3_lattices @ X12))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.91/1.12  thf('8', plain, ((l1_lattices @ sk_A)),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf('9', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.91/1.12            = (k4_lattices @ sk_A @ X0 @ sk_B_1))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.91/1.12  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('11', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | ((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.91/1.12              = (k4_lattices @ sk_A @ X0 @ sk_B_1)))),
% 0.91/1.12      inference('clc', [status(thm)], ['9', '10'])).
% 0.91/1.12  thf('12', plain,
% 0.91/1.12      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.91/1.12         = (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['1', '11'])).
% 0.91/1.12  thf('13', plain,
% 0.91/1.12      (~ (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 0.91/1.12      inference('demod', [status(thm)], ['0', '12'])).
% 0.91/1.12  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(redefinition_k4_lattices, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.91/1.12         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.91/1.12         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.91/1.12  thf('16', plain,
% 0.91/1.12      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.91/1.12          | ~ (l1_lattices @ X14)
% 0.91/1.12          | ~ (v6_lattices @ X14)
% 0.91/1.12          | (v2_struct_0 @ X14)
% 0.91/1.12          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.91/1.12          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.91/1.12  thf('17', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.91/1.12            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (v6_lattices @ sk_A)
% 0.91/1.12          | ~ (l1_lattices @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.12  thf('18', plain, ((v6_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('19', plain, ((l1_lattices @ sk_A)),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.91/1.12            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.91/1.12  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('22', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | ((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 0.91/1.12              = (k2_lattices @ sk_A @ sk_B_1 @ X0)))),
% 0.91/1.12      inference('clc', [status(thm)], ['20', '21'])).
% 0.91/1.12  thf('23', plain,
% 0.91/1.12      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.91/1.12         = (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['14', '22'])).
% 0.91/1.12  thf('24', plain,
% 0.91/1.12      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.91/1.12         = (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['1', '11'])).
% 0.91/1.12  thf('25', plain,
% 0.91/1.12      (((k2_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.91/1.12         = (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup+', [status(thm)], ['23', '24'])).
% 0.91/1.12  thf('26', plain,
% 0.91/1.12      (~ (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ sk_B_1)),
% 0.91/1.12      inference('demod', [status(thm)], ['13', '25'])).
% 0.91/1.12  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('28', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.91/1.12          | ~ (l1_lattices @ X14)
% 0.91/1.12          | ~ (v6_lattices @ X14)
% 0.91/1.12          | (v2_struct_0 @ X14)
% 0.91/1.12          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.91/1.12          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.91/1.12  thf('30', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_lattices @ sk_A @ sk_C_1 @ X0)
% 0.91/1.12            = (k2_lattices @ sk_A @ sk_C_1 @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (v6_lattices @ sk_A)
% 0.91/1.12          | ~ (l1_lattices @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.12  thf('31', plain, ((v6_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('32', plain, ((l1_lattices @ sk_A)),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf('33', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_lattices @ sk_A @ sk_C_1 @ X0)
% 0.91/1.12            = (k2_lattices @ sk_A @ sk_C_1 @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.91/1.12  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('35', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | ((k4_lattices @ sk_A @ sk_C_1 @ X0)
% 0.91/1.12              = (k2_lattices @ sk_A @ sk_C_1 @ X0)))),
% 0.91/1.12      inference('clc', [status(thm)], ['33', '34'])).
% 0.91/1.12  thf('36', plain,
% 0.91/1.12      (((k4_lattices @ sk_A @ sk_C_1 @ sk_B_1)
% 0.91/1.12         = (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['27', '35'])).
% 0.91/1.12  thf('37', plain,
% 0.91/1.12      (((k2_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.91/1.12         = (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup+', [status(thm)], ['23', '24'])).
% 0.91/1.12  thf('38', plain,
% 0.91/1.12      (((k2_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.91/1.12         = (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.12  thf('39', plain,
% 0.91/1.12      (~ (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 0.91/1.12      inference('demod', [status(thm)], ['26', '38'])).
% 0.91/1.12  thf('40', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('41', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(d8_lattices, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.91/1.12       ( ( v8_lattices @ A ) <=>
% 0.91/1.12         ( ![B:$i]:
% 0.91/1.12           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12             ( ![C:$i]:
% 0.91/1.12               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.91/1.12                   ( C ) ) ) ) ) ) ) ))).
% 0.91/1.12  thf('42', plain,
% 0.91/1.12      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.91/1.12         (~ (v8_lattices @ X6)
% 0.91/1.12          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.91/1.12          | ((k1_lattices @ X6 @ (k2_lattices @ X6 @ X8 @ X7) @ X7) = (X7))
% 0.91/1.12          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.91/1.12          | ~ (l3_lattices @ X6)
% 0.91/1.12          | (v2_struct_0 @ X6))),
% 0.91/1.12      inference('cnf', [status(esa)], [d8_lattices])).
% 0.91/1.12  thf('43', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (l3_lattices @ sk_A)
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 0.91/1.12              = (sk_B_1))
% 0.91/1.12          | ~ (v8_lattices @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['41', '42'])).
% 0.91/1.12  thf('44', plain, ((l3_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('45', plain, ((v8_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('46', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 0.91/1.12              = (sk_B_1)))),
% 0.91/1.12      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.91/1.12  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('48', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 0.91/1.12            = (sk_B_1))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('clc', [status(thm)], ['46', '47'])).
% 0.91/1.12  thf('49', plain,
% 0.91/1.12      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 0.91/1.12         = (sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '48'])).
% 0.91/1.12  thf('50', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('51', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(dt_k4_lattices, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.91/1.12         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.91/1.12         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12       ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.91/1.12  thf('52', plain,
% 0.91/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.91/1.12          | ~ (l1_lattices @ X10)
% 0.91/1.12          | ~ (v6_lattices @ X10)
% 0.91/1.12          | (v2_struct_0 @ X10)
% 0.91/1.12          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.91/1.12          | (m1_subset_1 @ (k4_lattices @ X10 @ X9 @ X11) @ (u1_struct_0 @ X10)))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k4_lattices])).
% 0.91/1.12  thf('53', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 0.91/1.12           (u1_struct_0 @ sk_A))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (v6_lattices @ sk_A)
% 0.91/1.12          | ~ (l1_lattices @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['51', '52'])).
% 0.91/1.12  thf('54', plain, ((v6_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('55', plain, ((l1_lattices @ sk_A)),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf('56', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 0.91/1.12           (u1_struct_0 @ sk_A))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (v2_struct_0 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.91/1.12  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('58', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 0.91/1.12             (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('clc', [status(thm)], ['56', '57'])).
% 0.91/1.12  thf('59', plain,
% 0.91/1.12      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 0.91/1.12        (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['50', '58'])).
% 0.91/1.12  thf('60', plain,
% 0.91/1.12      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 0.91/1.12         = (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['1', '11'])).
% 0.91/1.12  thf('61', plain,
% 0.91/1.12      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ 
% 0.91/1.12        (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['59', '60'])).
% 0.91/1.12  thf(d3_lattices, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12           ( ![C:$i]:
% 0.91/1.12             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.12               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.91/1.12                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.91/1.12  thf('62', plain,
% 0.91/1.12      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.91/1.12          | ((k1_lattices @ X4 @ X3 @ X5) != (X5))
% 0.91/1.12          | (r1_lattices @ X4 @ X3 @ X5)
% 0.91/1.12          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.91/1.12          | ~ (l2_lattices @ X4)
% 0.91/1.12          | (v2_struct_0 @ X4))),
% 0.91/1.12      inference('cnf', [status(esa)], [d3_lattices])).
% 0.91/1.12  thf('63', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (l2_lattices @ sk_A)
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 0.91/1.12          | ((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 0.91/1.12              != (X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['61', '62'])).
% 0.91/1.12  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('65', plain,
% 0.91/1.12      (![X12 : $i]: ((l2_lattices @ X12) | ~ (l3_lattices @ X12))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.91/1.12  thf('66', plain, ((l2_lattices @ sk_A)),
% 0.91/1.12      inference('sup-', [status(thm)], ['64', '65'])).
% 0.91/1.12  thf('67', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 0.91/1.12          | ((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 0.91/1.12              != (X0)))),
% 0.91/1.12      inference('demod', [status(thm)], ['63', '66'])).
% 0.91/1.12  thf('68', plain,
% 0.91/1.12      (((k4_lattices @ sk_A @ sk_C_1 @ sk_B_1)
% 0.91/1.12         = (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['27', '35'])).
% 0.91/1.12  thf('69', plain,
% 0.91/1.12      (((k4_lattices @ sk_A @ sk_C_1 @ sk_B_1)
% 0.91/1.12         = (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['27', '35'])).
% 0.91/1.12  thf('70', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((v2_struct_0 @ sk_A)
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.12          | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 0.91/1.12          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 0.91/1.12              != (X0)))),
% 0.91/1.12      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.91/1.12  thf('71', plain,
% 0.91/1.12      ((((sk_B_1) != (sk_B_1))
% 0.91/1.12        | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 0.91/1.12        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.91/1.12        | (v2_struct_0 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['49', '70'])).
% 0.91/1.12  thf('72', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('73', plain,
% 0.91/1.12      ((((sk_B_1) != (sk_B_1))
% 0.91/1.12        | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 0.91/1.12        | (v2_struct_0 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.12  thf('74', plain,
% 0.91/1.12      (((v2_struct_0 @ sk_A)
% 0.91/1.12        | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1))),
% 0.91/1.12      inference('simplify', [status(thm)], ['73'])).
% 0.91/1.12  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('76', plain,
% 0.91/1.12      ((r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 0.91/1.12      inference('clc', [status(thm)], ['74', '75'])).
% 0.91/1.12  thf('77', plain, ($false), inference('demod', [status(thm)], ['39', '76'])).
% 0.91/1.12  
% 0.91/1.12  % SZS output end Refutation
% 0.91/1.12  
% 0.91/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
