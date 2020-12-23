%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DLCgZdIHCZ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:31 EST 2020

% Result     : Theorem 55.08s
% Output     : Refutation 55.08s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 195 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          : 1034 (3666 expanded)
%              Number of equality atoms :   34 (  35 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t27_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_lattices @ A @ B @ C )
                   => ( r1_lattices @ A @ ( k2_lattices @ A @ B @ D ) @ ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattices @ A @ B @ C )
                     => ( r1_lattices @ A @ ( k2_lattices @ A @ B @ D ) @ ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_lattices])).

thf('0',plain,(
    ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k2_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k2_lattices @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattices])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
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
    ! [X16: $i] :
      ( ( l1_lattices @ X16 )
      | ~ ( l3_lattices @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('8',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','11'])).

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

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v8_lattices @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k1_lattices @ X7 @ ( k2_lattices @ X7 @ X9 @ X8 ) @ X8 )
        = X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
        = ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
        = ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
        = ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v7_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( k2_lattices @ A @ B @ ( k2_lattices @ A @ C @ D ) )
                      = ( k2_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( v7_lattices @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( ( k2_lattices @ X3 @ X5 @ ( k2_lattices @ X3 @ X4 @ X6 ) )
        = ( k2_lattices @ X3 @ ( k2_lattices @ X3 @ X5 @ X4 ) @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_lattices])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_3 @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ X1 ) )
      | ~ ( v7_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('27',plain,(
    v7_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_3 @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v9_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k2_lattices @ X10 @ X12 @ ( k1_lattices @ X10 @ X12 @ X11 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_3 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_3 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_3 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = sk_B_3 ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattices @ X1 @ X0 @ X2 )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_3 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( l2_lattices @ X16 )
      | ~ ( l3_lattices @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('46',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_3 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    | ( ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
      = sk_C_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    r1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
      = sk_C_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = sk_C_3 ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = sk_B_3 ),
    inference(demod,[status(thm)],['39','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_lattices @ sk_A @ sk_B_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','56'])).

thf('58',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k2_lattices @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattices])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
       != X2 )
      | ( r1_lattices @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 )
     != ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('74',plain,
    ( ( ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 )
     != ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DLCgZdIHCZ
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 55.08/55.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 55.08/55.30  % Solved by: fo/fo7.sh
% 55.08/55.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 55.08/55.30  % done 4097 iterations in 54.835s
% 55.08/55.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 55.08/55.30  % SZS output start Refutation
% 55.08/55.30  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 55.08/55.30  thf(sk_C_3_type, type, sk_C_3: $i).
% 55.08/55.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 55.08/55.30  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 55.08/55.30  thf(sk_B_3_type, type, sk_B_3: $i).
% 55.08/55.30  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 55.08/55.30  thf(sk_D_1_type, type, sk_D_1: $i).
% 55.08/55.30  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 55.08/55.30  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 55.08/55.30  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 55.08/55.30  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 55.08/55.30  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 55.08/55.30  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 55.08/55.30  thf(sk_A_type, type, sk_A: $i).
% 55.08/55.30  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 55.08/55.30  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 55.08/55.30  thf(t27_lattices, conjecture,
% 55.08/55.30    (![A:$i]:
% 55.08/55.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_lattices @ A ) & 
% 55.08/55.30         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 55.08/55.30       ( ![B:$i]:
% 55.08/55.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30           ( ![C:$i]:
% 55.08/55.30             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30               ( ![D:$i]:
% 55.08/55.30                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30                   ( ( r1_lattices @ A @ B @ C ) =>
% 55.08/55.30                     ( r1_lattices @
% 55.08/55.30                       A @ ( k2_lattices @ A @ B @ D ) @ 
% 55.08/55.30                       ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 55.08/55.30  thf(zf_stmt_0, negated_conjecture,
% 55.08/55.30    (~( ![A:$i]:
% 55.08/55.30        ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_lattices @ A ) & 
% 55.08/55.30            ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 55.08/55.30          ( ![B:$i]:
% 55.08/55.30            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30              ( ![C:$i]:
% 55.08/55.30                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30                  ( ![D:$i]:
% 55.08/55.30                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30                      ( ( r1_lattices @ A @ B @ C ) =>
% 55.08/55.30                        ( r1_lattices @
% 55.08/55.30                          A @ ( k2_lattices @ A @ B @ D ) @ 
% 55.08/55.30                          ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 55.08/55.30    inference('cnf.neg', [status(esa)], [t27_lattices])).
% 55.08/55.30  thf('0', plain,
% 55.08/55.30      (~ (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ 
% 55.08/55.30          (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('1', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('2', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('3', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf(dt_k2_lattices, axiom,
% 55.08/55.30    (![A:$i,B:$i,C:$i]:
% 55.08/55.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) & 
% 55.08/55.30         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 55.08/55.30         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 55.08/55.30       ( m1_subset_1 @ ( k2_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 55.08/55.30  thf('4', plain,
% 55.08/55.30      (![X13 : $i, X14 : $i, X15 : $i]:
% 55.08/55.30         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 55.08/55.30          | ~ (l1_lattices @ X14)
% 55.08/55.30          | (v2_struct_0 @ X14)
% 55.08/55.30          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 55.08/55.30          | (m1_subset_1 @ (k2_lattices @ X14 @ X13 @ X15) @ 
% 55.08/55.30             (u1_struct_0 @ X14)))),
% 55.08/55.30      inference('cnf', [status(esa)], [dt_k2_lattices])).
% 55.08/55.30  thf('5', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_3 @ X0) @ 
% 55.08/55.30           (u1_struct_0 @ sk_A))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (l1_lattices @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['3', '4'])).
% 55.08/55.30  thf('6', plain, ((l3_lattices @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf(dt_l3_lattices, axiom,
% 55.08/55.30    (![A:$i]:
% 55.08/55.30     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 55.08/55.30  thf('7', plain, (![X16 : $i]: ((l1_lattices @ X16) | ~ (l3_lattices @ X16))),
% 55.08/55.30      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 55.08/55.30  thf('8', plain, ((l1_lattices @ sk_A)),
% 55.08/55.30      inference('sup-', [status(thm)], ['6', '7'])).
% 55.08/55.30  thf('9', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_3 @ X0) @ 
% 55.08/55.30           (u1_struct_0 @ sk_A))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('demod', [status(thm)], ['5', '8'])).
% 55.08/55.30  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('11', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_3 @ X0) @ 
% 55.08/55.30             (u1_struct_0 @ sk_A)))),
% 55.08/55.30      inference('clc', [status(thm)], ['9', '10'])).
% 55.08/55.30  thf('12', plain,
% 55.08/55.30      ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1) @ 
% 55.08/55.30        (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['2', '11'])).
% 55.08/55.30  thf(d8_lattices, axiom,
% 55.08/55.30    (![A:$i]:
% 55.08/55.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 55.08/55.30       ( ( v8_lattices @ A ) <=>
% 55.08/55.30         ( ![B:$i]:
% 55.08/55.30           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30             ( ![C:$i]:
% 55.08/55.30               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 55.08/55.30                   ( C ) ) ) ) ) ) ) ))).
% 55.08/55.30  thf('13', plain,
% 55.08/55.30      (![X7 : $i, X8 : $i, X9 : $i]:
% 55.08/55.30         (~ (v8_lattices @ X7)
% 55.08/55.30          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 55.08/55.30          | ((k1_lattices @ X7 @ (k2_lattices @ X7 @ X9 @ X8) @ X8) = (X8))
% 55.08/55.30          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 55.08/55.30          | ~ (l3_lattices @ X7)
% 55.08/55.30          | (v2_struct_0 @ X7))),
% 55.08/55.30      inference('cnf', [status(esa)], [d8_lattices])).
% 55.08/55.30  thf('14', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (l3_lattices @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k1_lattices @ sk_A @ 
% 55.08/55.30              (k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)) @ 
% 55.08/55.30              (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30              = (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30          | ~ (v8_lattices @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['12', '13'])).
% 55.08/55.30  thf('15', plain, ((l3_lattices @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('16', plain, ((v8_lattices @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('17', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k1_lattices @ sk_A @ 
% 55.08/55.30              (k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)) @ 
% 55.08/55.30              (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30              = (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)))),
% 55.08/55.30      inference('demod', [status(thm)], ['14', '15', '16'])).
% 55.08/55.30  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('19', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         (((k1_lattices @ sk_A @ 
% 55.08/55.30            (k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)) @ 
% 55.08/55.30            (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30            = (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 55.08/55.30      inference('clc', [status(thm)], ['17', '18'])).
% 55.08/55.30  thf('20', plain,
% 55.08/55.30      (((k1_lattices @ sk_A @ 
% 55.08/55.30         (k2_lattices @ sk_A @ sk_B_3 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)) @ 
% 55.08/55.30         (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30         = (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))),
% 55.08/55.30      inference('sup-', [status(thm)], ['1', '19'])).
% 55.08/55.30  thf('21', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('22', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('23', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf(d7_lattices, axiom,
% 55.08/55.30    (![A:$i]:
% 55.08/55.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 55.08/55.30       ( ( v7_lattices @ A ) <=>
% 55.08/55.30         ( ![B:$i]:
% 55.08/55.30           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30             ( ![C:$i]:
% 55.08/55.30               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30                 ( ![D:$i]:
% 55.08/55.30                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30                     ( ( k2_lattices @ A @ B @ ( k2_lattices @ A @ C @ D ) ) =
% 55.08/55.30                       ( k2_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 55.08/55.30  thf('24', plain,
% 55.08/55.30      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 55.08/55.30         (~ (v7_lattices @ X3)
% 55.08/55.30          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 55.08/55.30          | ((k2_lattices @ X3 @ X5 @ (k2_lattices @ X3 @ X4 @ X6))
% 55.08/55.30              = (k2_lattices @ X3 @ (k2_lattices @ X3 @ X5 @ X4) @ X6))
% 55.08/55.30          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X3))
% 55.08/55.30          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 55.08/55.30          | ~ (l1_lattices @ X3)
% 55.08/55.30          | (v2_struct_0 @ X3))),
% 55.08/55.30      inference('cnf', [status(esa)], [d7_lattices])).
% 55.08/55.30  thf('25', plain,
% 55.08/55.30      (![X0 : $i, X1 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (l1_lattices @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_3 @ X1))
% 55.08/55.30              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ X1))
% 55.08/55.30          | ~ (v7_lattices @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['23', '24'])).
% 55.08/55.30  thf('26', plain, ((l1_lattices @ sk_A)),
% 55.08/55.30      inference('sup-', [status(thm)], ['6', '7'])).
% 55.08/55.30  thf('27', plain, ((v7_lattices @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('28', plain,
% 55.08/55.30      (![X0 : $i, X1 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_3 @ X1))
% 55.08/55.30              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ X1)))),
% 55.08/55.30      inference('demod', [status(thm)], ['25', '26', '27'])).
% 55.08/55.30  thf('29', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         (((k2_lattices @ sk_A @ sk_B_3 @ (k2_lattices @ sk_A @ sk_C_3 @ X0))
% 55.08/55.30            = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_C_3) @ X0))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['22', '28'])).
% 55.08/55.30  thf('30', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('31', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf(d9_lattices, axiom,
% 55.08/55.30    (![A:$i]:
% 55.08/55.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 55.08/55.30       ( ( v9_lattices @ A ) <=>
% 55.08/55.30         ( ![B:$i]:
% 55.08/55.30           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30             ( ![C:$i]:
% 55.08/55.30               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 55.08/55.30                   ( B ) ) ) ) ) ) ) ))).
% 55.08/55.30  thf('32', plain,
% 55.08/55.30      (![X10 : $i, X11 : $i, X12 : $i]:
% 55.08/55.30         (~ (v9_lattices @ X10)
% 55.08/55.30          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 55.08/55.30          | ((k2_lattices @ X10 @ X12 @ (k1_lattices @ X10 @ X12 @ X11))
% 55.08/55.30              = (X12))
% 55.08/55.30          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 55.08/55.30          | ~ (l3_lattices @ X10)
% 55.08/55.30          | (v2_struct_0 @ X10))),
% 55.08/55.30      inference('cnf', [status(esa)], [d9_lattices])).
% 55.08/55.30  thf('33', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (l3_lattices @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_3))
% 55.08/55.30              = (X0))
% 55.08/55.30          | ~ (v9_lattices @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['31', '32'])).
% 55.08/55.30  thf('34', plain, ((l3_lattices @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('35', plain, ((v9_lattices @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('36', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_3))
% 55.08/55.30              = (X0)))),
% 55.08/55.30      inference('demod', [status(thm)], ['33', '34', '35'])).
% 55.08/55.30  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('38', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_3))
% 55.08/55.30            = (X0))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 55.08/55.30      inference('clc', [status(thm)], ['36', '37'])).
% 55.08/55.30  thf('39', plain,
% 55.08/55.30      (((k2_lattices @ sk_A @ sk_B_3 @ (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 55.08/55.30         = (sk_B_3))),
% 55.08/55.30      inference('sup-', [status(thm)], ['30', '38'])).
% 55.08/55.30  thf('40', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('41', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf(d3_lattices, axiom,
% 55.08/55.30    (![A:$i]:
% 55.08/55.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 55.08/55.30       ( ![B:$i]:
% 55.08/55.30         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30           ( ![C:$i]:
% 55.08/55.30             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 55.08/55.30               ( ( r1_lattices @ A @ B @ C ) <=>
% 55.08/55.30                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 55.08/55.30  thf('42', plain,
% 55.08/55.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.08/55.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 55.08/55.30          | ~ (r1_lattices @ X1 @ X0 @ X2)
% 55.08/55.30          | ((k1_lattices @ X1 @ X0 @ X2) = (X2))
% 55.08/55.30          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 55.08/55.30          | ~ (l2_lattices @ X1)
% 55.08/55.30          | (v2_struct_0 @ X1))),
% 55.08/55.30      inference('cnf', [status(esa)], [d3_lattices])).
% 55.08/55.30  thf('43', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (l2_lattices @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k1_lattices @ sk_A @ sk_B_3 @ X0) = (X0))
% 55.08/55.30          | ~ (r1_lattices @ sk_A @ sk_B_3 @ X0))),
% 55.08/55.30      inference('sup-', [status(thm)], ['41', '42'])).
% 55.08/55.30  thf('44', plain, ((l3_lattices @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('45', plain,
% 55.08/55.30      (![X16 : $i]: ((l2_lattices @ X16) | ~ (l3_lattices @ X16))),
% 55.08/55.30      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 55.08/55.30  thf('46', plain, ((l2_lattices @ sk_A)),
% 55.08/55.30      inference('sup-', [status(thm)], ['44', '45'])).
% 55.08/55.30  thf('47', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k1_lattices @ sk_A @ sk_B_3 @ X0) = (X0))
% 55.08/55.30          | ~ (r1_lattices @ sk_A @ sk_B_3 @ X0))),
% 55.08/55.30      inference('demod', [status(thm)], ['43', '46'])).
% 55.08/55.30  thf('48', plain,
% 55.08/55.30      ((~ (r1_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 55.08/55.30        | ((k1_lattices @ sk_A @ sk_B_3 @ sk_C_3) = (sk_C_3))
% 55.08/55.30        | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['40', '47'])).
% 55.08/55.30  thf('49', plain, ((r1_lattices @ sk_A @ sk_B_3 @ sk_C_3)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('50', plain,
% 55.08/55.30      ((((k1_lattices @ sk_A @ sk_B_3 @ sk_C_3) = (sk_C_3))
% 55.08/55.30        | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('demod', [status(thm)], ['48', '49'])).
% 55.08/55.30  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('52', plain, (((k1_lattices @ sk_A @ sk_B_3 @ sk_C_3) = (sk_C_3))),
% 55.08/55.30      inference('clc', [status(thm)], ['50', '51'])).
% 55.08/55.30  thf('53', plain, (((k2_lattices @ sk_A @ sk_B_3 @ sk_C_3) = (sk_B_3))),
% 55.08/55.30      inference('demod', [status(thm)], ['39', '52'])).
% 55.08/55.30  thf('54', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         (((k2_lattices @ sk_A @ sk_B_3 @ (k2_lattices @ sk_A @ sk_C_3 @ X0))
% 55.08/55.30            = (k2_lattices @ sk_A @ sk_B_3 @ X0))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('demod', [status(thm)], ['29', '53'])).
% 55.08/55.30  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('56', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | ((k2_lattices @ sk_A @ sk_B_3 @ (k2_lattices @ sk_A @ sk_C_3 @ X0))
% 55.08/55.30              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 55.08/55.30      inference('clc', [status(thm)], ['54', '55'])).
% 55.08/55.30  thf('57', plain,
% 55.08/55.30      (((k2_lattices @ sk_A @ sk_B_3 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30         = (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 55.08/55.30      inference('sup-', [status(thm)], ['21', '56'])).
% 55.08/55.30  thf('58', plain,
% 55.08/55.30      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ 
% 55.08/55.30         (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30         = (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))),
% 55.08/55.30      inference('demod', [status(thm)], ['20', '57'])).
% 55.08/55.30  thf('59', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('60', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('61', plain,
% 55.08/55.30      (![X13 : $i, X14 : $i, X15 : $i]:
% 55.08/55.30         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 55.08/55.30          | ~ (l1_lattices @ X14)
% 55.08/55.30          | (v2_struct_0 @ X14)
% 55.08/55.30          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 55.08/55.30          | (m1_subset_1 @ (k2_lattices @ X14 @ X13 @ X15) @ 
% 55.08/55.30             (u1_struct_0 @ X14)))),
% 55.08/55.30      inference('cnf', [status(esa)], [dt_k2_lattices])).
% 55.08/55.30  thf('62', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_3 @ X0) @ 
% 55.08/55.30           (u1_struct_0 @ sk_A))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (l1_lattices @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['60', '61'])).
% 55.08/55.30  thf('63', plain, ((l1_lattices @ sk_A)),
% 55.08/55.30      inference('sup-', [status(thm)], ['6', '7'])).
% 55.08/55.30  thf('64', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_3 @ X0) @ 
% 55.08/55.30           (u1_struct_0 @ sk_A))
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('demod', [status(thm)], ['62', '63'])).
% 55.08/55.30  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('66', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_3 @ X0) @ 
% 55.08/55.30             (u1_struct_0 @ sk_A)))),
% 55.08/55.30      inference('clc', [status(thm)], ['64', '65'])).
% 55.08/55.30  thf('67', plain,
% 55.08/55.30      ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ 
% 55.08/55.30        (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['59', '66'])).
% 55.08/55.30  thf('68', plain,
% 55.08/55.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.08/55.30         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 55.08/55.30          | ((k1_lattices @ X1 @ X0 @ X2) != (X2))
% 55.08/55.30          | (r1_lattices @ X1 @ X0 @ X2)
% 55.08/55.30          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 55.08/55.30          | ~ (l2_lattices @ X1)
% 55.08/55.30          | (v2_struct_0 @ X1))),
% 55.08/55.30      inference('cnf', [status(esa)], [d3_lattices])).
% 55.08/55.30  thf('69', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (l2_lattices @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ X0)
% 55.08/55.30          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ X0)
% 55.08/55.30              != (X0)))),
% 55.08/55.30      inference('sup-', [status(thm)], ['67', '68'])).
% 55.08/55.30  thf('70', plain, ((l2_lattices @ sk_A)),
% 55.08/55.30      inference('sup-', [status(thm)], ['44', '45'])).
% 55.08/55.30  thf('71', plain,
% 55.08/55.30      (![X0 : $i]:
% 55.08/55.30         ((v2_struct_0 @ sk_A)
% 55.08/55.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 55.08/55.30          | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ X0)
% 55.08/55.30          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ X0)
% 55.08/55.30              != (X0)))),
% 55.08/55.30      inference('demod', [status(thm)], ['69', '70'])).
% 55.08/55.30  thf('72', plain,
% 55.08/55.30      ((((k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)
% 55.08/55.30          != (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30        | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ 
% 55.08/55.30           (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30        | ~ (m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1) @ 
% 55.08/55.30             (u1_struct_0 @ sk_A))
% 55.08/55.30        | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['58', '71'])).
% 55.08/55.30  thf('73', plain,
% 55.08/55.30      ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1) @ 
% 55.08/55.30        (u1_struct_0 @ sk_A))),
% 55.08/55.30      inference('sup-', [status(thm)], ['2', '11'])).
% 55.08/55.30  thf('74', plain,
% 55.08/55.30      ((((k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)
% 55.08/55.30          != (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30        | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ 
% 55.08/55.30           (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))
% 55.08/55.30        | (v2_struct_0 @ sk_A))),
% 55.08/55.30      inference('demod', [status(thm)], ['72', '73'])).
% 55.08/55.30  thf('75', plain,
% 55.08/55.30      (((v2_struct_0 @ sk_A)
% 55.08/55.30        | (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ 
% 55.08/55.30           (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)))),
% 55.08/55.30      inference('simplify', [status(thm)], ['74'])).
% 55.08/55.30  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 55.08/55.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.08/55.30  thf('77', plain,
% 55.08/55.30      ((r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ 
% 55.08/55.30        (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))),
% 55.08/55.30      inference('clc', [status(thm)], ['75', '76'])).
% 55.08/55.30  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 55.08/55.30  
% 55.08/55.30  % SZS output end Refutation
% 55.08/55.30  
% 55.08/55.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
