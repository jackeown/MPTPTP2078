%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P4ddaqhBFA

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:31 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 181 expanded)
%              Number of leaves         :   22 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  792 (2448 expanded)
%              Number of equality atoms :   32 (  38 expanded)
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

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v8_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k1_lattices @ X6 @ ( k2_lattices @ X6 @ X8 @ X7 ) @ X7 )
        = X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_1 ) @ sk_B_1 )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k2_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['23','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k2_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k2_lattices @ X10 @ X9 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattices])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v6_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('55',plain,
    ( ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','55'])).

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

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ X3 @ X5 )
       != X5 )
      | ( r1_lattices @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l2_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X12: $i] :
      ( ( l2_lattices @ X12 )
      | ~ ( l3_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('61',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['13','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P4ddaqhBFA
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.04/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.04/1.21  % Solved by: fo/fo7.sh
% 1.04/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.21  % done 346 iterations in 0.746s
% 1.04/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.04/1.21  % SZS output start Refutation
% 1.04/1.21  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 1.04/1.21  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 1.04/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.04/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.21  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 1.04/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.04/1.21  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 1.04/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.04/1.21  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 1.04/1.21  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 1.04/1.21  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.04/1.21  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 1.04/1.21  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 1.04/1.21  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 1.04/1.21  thf(t23_lattices, conjecture,
% 1.04/1.21    (![A:$i]:
% 1.04/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.04/1.21         ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.04/1.21       ( ![B:$i]:
% 1.04/1.21         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21           ( ![C:$i]:
% 1.04/1.21             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21               ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ))).
% 1.04/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.21    (~( ![A:$i]:
% 1.04/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.04/1.21            ( v8_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.04/1.21          ( ![B:$i]:
% 1.04/1.21            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21              ( ![C:$i]:
% 1.04/1.21                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21                  ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) ) ) )),
% 1.04/1.21    inference('cnf.neg', [status(esa)], [t23_lattices])).
% 1.04/1.21  thf('0', plain,
% 1.04/1.21      (~ (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ sk_B_1)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf(commutativity_k4_lattices, axiom,
% 1.04/1.21    (![A:$i,B:$i,C:$i]:
% 1.04/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.04/1.21         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.04/1.21         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.21       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 1.04/1.21  thf('3', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 1.04/1.21          | ~ (l1_lattices @ X1)
% 1.04/1.21          | ~ (v6_lattices @ X1)
% 1.04/1.21          | (v2_struct_0 @ X1)
% 1.04/1.21          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 1.04/1.21          | ((k4_lattices @ X1 @ X0 @ X2) = (k4_lattices @ X1 @ X2 @ X0)))),
% 1.04/1.21      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 1.04/1.21  thf('4', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.04/1.21            = (k4_lattices @ sk_A @ X0 @ sk_B_1))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (v6_lattices @ sk_A)
% 1.04/1.21          | ~ (l1_lattices @ sk_A))),
% 1.04/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 1.04/1.21  thf('5', plain, ((v6_lattices @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('6', plain, ((l3_lattices @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf(dt_l3_lattices, axiom,
% 1.04/1.21    (![A:$i]:
% 1.04/1.21     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 1.04/1.21  thf('7', plain, (![X12 : $i]: ((l1_lattices @ X12) | ~ (l3_lattices @ X12))),
% 1.04/1.21      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 1.04/1.21  thf('8', plain, ((l1_lattices @ sk_A)),
% 1.04/1.21      inference('sup-', [status(thm)], ['6', '7'])).
% 1.04/1.21  thf('9', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.04/1.21            = (k4_lattices @ sk_A @ X0 @ sk_B_1))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.04/1.21  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('11', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | ((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.04/1.21              = (k4_lattices @ sk_A @ X0 @ sk_B_1)))),
% 1.04/1.21      inference('clc', [status(thm)], ['9', '10'])).
% 1.04/1.21  thf('12', plain,
% 1.04/1.21      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.04/1.21         = (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 1.04/1.21      inference('sup-', [status(thm)], ['1', '11'])).
% 1.04/1.21  thf('13', plain,
% 1.04/1.21      (~ (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 1.04/1.21      inference('demod', [status(thm)], ['0', '12'])).
% 1.04/1.21  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf(d8_lattices, axiom,
% 1.04/1.21    (![A:$i]:
% 1.04/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.04/1.21       ( ( v8_lattices @ A ) <=>
% 1.04/1.21         ( ![B:$i]:
% 1.04/1.21           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21             ( ![C:$i]:
% 1.04/1.21               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 1.04/1.21                   ( C ) ) ) ) ) ) ) ))).
% 1.04/1.21  thf('16', plain,
% 1.04/1.21      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.04/1.21         (~ (v8_lattices @ X6)
% 1.04/1.21          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 1.04/1.21          | ((k1_lattices @ X6 @ (k2_lattices @ X6 @ X8 @ X7) @ X7) = (X7))
% 1.04/1.21          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 1.04/1.21          | ~ (l3_lattices @ X6)
% 1.04/1.21          | (v2_struct_0 @ X6))),
% 1.04/1.21      inference('cnf', [status(esa)], [d8_lattices])).
% 1.04/1.21  thf('17', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         ((v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (l3_lattices @ sk_A)
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 1.04/1.21              = (sk_B_1))
% 1.04/1.21          | ~ (v8_lattices @ sk_A))),
% 1.04/1.21      inference('sup-', [status(thm)], ['15', '16'])).
% 1.04/1.21  thf('18', plain, ((l3_lattices @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('19', plain, ((v8_lattices @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('20', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         ((v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 1.04/1.21              = (sk_B_1)))),
% 1.04/1.21      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.04/1.21  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('22', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_1) @ sk_B_1)
% 1.04/1.21            = (sk_B_1))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.21      inference('clc', [status(thm)], ['20', '21'])).
% 1.04/1.21  thf('23', plain,
% 1.04/1.21      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 1.04/1.21         = (sk_B_1))),
% 1.04/1.21      inference('sup-', [status(thm)], ['14', '22'])).
% 1.04/1.21  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('25', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf(redefinition_k4_lattices, axiom,
% 1.04/1.21    (![A:$i,B:$i,C:$i]:
% 1.04/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.04/1.21         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.04/1.21         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.21       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 1.04/1.21  thf('26', plain,
% 1.04/1.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.04/1.21          | ~ (l1_lattices @ X14)
% 1.04/1.21          | ~ (v6_lattices @ X14)
% 1.04/1.21          | (v2_struct_0 @ X14)
% 1.04/1.21          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 1.04/1.21          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 1.04/1.21      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 1.04/1.21  thf('27', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (((k4_lattices @ sk_A @ sk_C_1 @ X0)
% 1.04/1.21            = (k2_lattices @ sk_A @ sk_C_1 @ X0))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (v6_lattices @ sk_A)
% 1.04/1.21          | ~ (l1_lattices @ sk_A))),
% 1.04/1.21      inference('sup-', [status(thm)], ['25', '26'])).
% 1.04/1.21  thf('28', plain, ((v6_lattices @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('29', plain, ((l1_lattices @ sk_A)),
% 1.04/1.21      inference('sup-', [status(thm)], ['6', '7'])).
% 1.04/1.21  thf('30', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (((k4_lattices @ sk_A @ sk_C_1 @ X0)
% 1.04/1.21            = (k2_lattices @ sk_A @ sk_C_1 @ X0))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.04/1.21  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('32', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | ((k4_lattices @ sk_A @ sk_C_1 @ X0)
% 1.04/1.21              = (k2_lattices @ sk_A @ sk_C_1 @ X0)))),
% 1.04/1.21      inference('clc', [status(thm)], ['30', '31'])).
% 1.04/1.21  thf('33', plain,
% 1.04/1.21      (((k4_lattices @ sk_A @ sk_C_1 @ sk_B_1)
% 1.04/1.21         = (k2_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 1.04/1.21      inference('sup-', [status(thm)], ['24', '32'])).
% 1.04/1.21  thf('34', plain,
% 1.04/1.21      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 1.04/1.21         = (sk_B_1))),
% 1.04/1.21      inference('demod', [status(thm)], ['23', '33'])).
% 1.04/1.21  thf('35', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('36', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf(dt_k2_lattices, axiom,
% 1.04/1.21    (![A:$i,B:$i,C:$i]:
% 1.04/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) & 
% 1.04/1.21         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.04/1.21         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.21       ( m1_subset_1 @ ( k2_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 1.04/1.21  thf('37', plain,
% 1.04/1.21      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 1.04/1.21          | ~ (l1_lattices @ X10)
% 1.04/1.21          | (v2_struct_0 @ X10)
% 1.04/1.21          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 1.04/1.21          | (m1_subset_1 @ (k2_lattices @ X10 @ X9 @ X11) @ (u1_struct_0 @ X10)))),
% 1.04/1.21      inference('cnf', [status(esa)], [dt_k2_lattices])).
% 1.04/1.21  thf('38', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 1.04/1.21           (u1_struct_0 @ sk_A))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (l1_lattices @ sk_A))),
% 1.04/1.21      inference('sup-', [status(thm)], ['36', '37'])).
% 1.04/1.21  thf('39', plain, ((l1_lattices @ sk_A)),
% 1.04/1.21      inference('sup-', [status(thm)], ['6', '7'])).
% 1.04/1.21  thf('40', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 1.04/1.21           (u1_struct_0 @ sk_A))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['38', '39'])).
% 1.04/1.21  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('42', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_1 @ X0) @ 
% 1.04/1.21             (u1_struct_0 @ sk_A)))),
% 1.04/1.21      inference('clc', [status(thm)], ['40', '41'])).
% 1.04/1.21  thf('43', plain,
% 1.04/1.21      ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 1.04/1.21        (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('sup-', [status(thm)], ['35', '42'])).
% 1.04/1.21  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('45', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('46', plain,
% 1.04/1.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.04/1.21          | ~ (l1_lattices @ X14)
% 1.04/1.21          | ~ (v6_lattices @ X14)
% 1.04/1.21          | (v2_struct_0 @ X14)
% 1.04/1.21          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 1.04/1.21          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 1.04/1.21      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 1.04/1.21  thf('47', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.04/1.21            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (v6_lattices @ sk_A)
% 1.04/1.21          | ~ (l1_lattices @ sk_A))),
% 1.04/1.21      inference('sup-', [status(thm)], ['45', '46'])).
% 1.04/1.21  thf('48', plain, ((v6_lattices @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('49', plain, ((l1_lattices @ sk_A)),
% 1.04/1.21      inference('sup-', [status(thm)], ['6', '7'])).
% 1.04/1.21  thf('50', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.04/1.21            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (v2_struct_0 @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.04/1.21  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('52', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | ((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.04/1.21              = (k2_lattices @ sk_A @ sk_B_1 @ X0)))),
% 1.04/1.21      inference('clc', [status(thm)], ['50', '51'])).
% 1.04/1.21  thf('53', plain,
% 1.04/1.21      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.04/1.21         = (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.04/1.21      inference('sup-', [status(thm)], ['44', '52'])).
% 1.04/1.21  thf('54', plain,
% 1.04/1.21      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.04/1.21         = (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 1.04/1.21      inference('sup-', [status(thm)], ['1', '11'])).
% 1.04/1.21  thf('55', plain,
% 1.04/1.21      (((k4_lattices @ sk_A @ sk_C_1 @ sk_B_1)
% 1.04/1.21         = (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.04/1.21      inference('demod', [status(thm)], ['53', '54'])).
% 1.04/1.21  thf('56', plain,
% 1.04/1.21      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ 
% 1.04/1.21        (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['43', '55'])).
% 1.04/1.21  thf(d3_lattices, axiom,
% 1.04/1.21    (![A:$i]:
% 1.04/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 1.04/1.21       ( ![B:$i]:
% 1.04/1.21         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21           ( ![C:$i]:
% 1.04/1.21             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.21               ( ( r1_lattices @ A @ B @ C ) <=>
% 1.04/1.21                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 1.04/1.21  thf('57', plain,
% 1.04/1.21      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.21         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 1.04/1.21          | ((k1_lattices @ X4 @ X3 @ X5) != (X5))
% 1.04/1.21          | (r1_lattices @ X4 @ X3 @ X5)
% 1.04/1.21          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 1.04/1.21          | ~ (l2_lattices @ X4)
% 1.04/1.21          | (v2_struct_0 @ X4))),
% 1.04/1.21      inference('cnf', [status(esa)], [d3_lattices])).
% 1.04/1.21  thf('58', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         ((v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (l2_lattices @ sk_A)
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 1.04/1.21          | ((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 1.04/1.21              != (X0)))),
% 1.04/1.21      inference('sup-', [status(thm)], ['56', '57'])).
% 1.04/1.21  thf('59', plain, ((l3_lattices @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('60', plain,
% 1.04/1.21      (![X12 : $i]: ((l2_lattices @ X12) | ~ (l3_lattices @ X12))),
% 1.04/1.21      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 1.04/1.21  thf('61', plain, ((l2_lattices @ sk_A)),
% 1.04/1.21      inference('sup-', [status(thm)], ['59', '60'])).
% 1.04/1.21  thf('62', plain,
% 1.04/1.21      (![X0 : $i]:
% 1.04/1.21         ((v2_struct_0 @ sk_A)
% 1.04/1.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.21          | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 1.04/1.21          | ((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ X0)
% 1.04/1.21              != (X0)))),
% 1.04/1.21      inference('demod', [status(thm)], ['58', '61'])).
% 1.04/1.21  thf('63', plain,
% 1.04/1.21      ((((sk_B_1) != (sk_B_1))
% 1.04/1.21        | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 1.04/1.21        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 1.04/1.21        | (v2_struct_0 @ sk_A))),
% 1.04/1.21      inference('sup-', [status(thm)], ['34', '62'])).
% 1.04/1.21  thf('64', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('65', plain,
% 1.04/1.21      ((((sk_B_1) != (sk_B_1))
% 1.04/1.21        | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)
% 1.04/1.21        | (v2_struct_0 @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['63', '64'])).
% 1.04/1.21  thf('66', plain,
% 1.04/1.21      (((v2_struct_0 @ sk_A)
% 1.04/1.21        | (r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1))),
% 1.04/1.21      inference('simplify', [status(thm)], ['65'])).
% 1.04/1.21  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('68', plain,
% 1.04/1.21      ((r1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 1.04/1.21      inference('clc', [status(thm)], ['66', '67'])).
% 1.04/1.21  thf('69', plain, ($false), inference('demod', [status(thm)], ['13', '68'])).
% 1.04/1.21  
% 1.04/1.21  % SZS output end Refutation
% 1.04/1.21  
% 1.04/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
