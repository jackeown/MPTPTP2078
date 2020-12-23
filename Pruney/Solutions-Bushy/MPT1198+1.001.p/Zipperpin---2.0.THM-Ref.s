%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1198+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dy6tJypzyC

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 127 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  594 (2252 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(t25_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_lattices @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_lattices @ A @ B @ C )
                      & ( r1_lattices @ A @ C @ D ) )
                   => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v5_lattices @ A )
          & ( l2_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r1_lattices @ A @ B @ C )
                        & ( r1_lattices @ A @ C @ D ) )
                     => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_C_1 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X0 @ sk_C_1 ) @ X1 ) )
      | ~ ( v5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_C_1 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ X0 @ sk_C_1 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_C_1 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattices @ X1 @ X0 @ X2 )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_C_1 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_C_1 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_C_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ ( k1_lattices @ sk_A @ sk_C_1 @ sk_D_1 ) )
    = ( k1_lattices @ sk_A @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_lattices @ X1 @ X0 @ X2 )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_C_1 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ sk_C_1 @ X0 )
        = X0 )
      | ~ ( r1_lattices @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_C_1 @ sk_D_1 )
    | ( ( k1_lattices @ sk_A @ sk_C_1 @ sk_D_1 )
      = sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    r1_lattices @ sk_A @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_lattices @ sk_A @ sk_C_1 @ sk_D_1 )
      = sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_lattices @ sk_A @ sk_C_1 @ sk_D_1 )
    = sk_D_1 ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_lattices @ sk_A @ sk_C_1 @ sk_D_1 )
    = sk_D_1 ),
    inference(clc,[status(thm)],['32','33'])).

thf('36',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_D_1 )
    = sk_D_1 ),
    inference(demod,[status(thm)],['23','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    l2_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_1 @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_D_1 )
     != sk_D_1 )
    | ( r1_lattices @ sk_A @ sk_B_1 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ~ ( r1_lattices @ sk_A @ sk_B_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_D_1 )
     != sk_D_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k1_lattices @ sk_A @ sk_B_1 @ sk_D_1 )
 != sk_D_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','47'])).


%------------------------------------------------------------------------------
