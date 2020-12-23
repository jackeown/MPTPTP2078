%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1195+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V2lTXZBp4n

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 191 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  662 (2901 expanded)
%              Number of equality atoms :   44 ( 143 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(t21_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k2_lattices @ A @ B @ C )
                  = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_lattices @ A @ B @ C )
                <=> ( ( k2_lattices @ A @ B @ C )
                    = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v9_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k2_lattices @ X6 @ X8 @ ( k1_lattices @ X6 @ X8 @ X7 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_2 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_2 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_2 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 )
    | ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
   <= ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattices @ X1 @ X0 @ X2 )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( l2_lattices @ X9 )
      | ~ ( l3_lattices @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('18',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    | ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_C_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_C_2 )
    | ~ ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_C_2 )
   <= ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != sk_B_2 )
    | ~ ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != sk_B_2 )
    | ~ ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 )
   <= ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 ) ),
    inference(split,[status(esa)],['10'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v8_lattices @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( ( k1_lattices @ X3 @ ( k2_lattices @ X3 @ X5 @ X4 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l3_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ sk_C_2 )
        = sk_C_2 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ sk_C_2 )
        = sk_C_2 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ sk_C_2 )
        = sk_C_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ sk_C_2 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_C_2 )
   <= ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 ) ),
    inference('sup+',[status(thm)],['26','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
       != X2 )
      | ( r1_lattices @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_2 @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != sk_C_2 )
    | ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    | ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != sk_C_2 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
   <= ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
   <= ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
   <= ~ ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('50',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    | ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    | ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 ) ),
    inference(split,[status(esa)],['10'])).

thf('52',plain,(
    r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['25','50','51'])).

thf('53',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = sk_C_2 ),
    inference(simpl_trail,[status(thm)],['23','52'])).

thf('54',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['9','53'])).

thf('55',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != sk_B_2 )
   <= ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
     != sk_B_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('56',plain,(
    ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
 != sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['25','50'])).

thf('57',plain,(
    ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
 != sk_B_2 ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).


%------------------------------------------------------------------------------
