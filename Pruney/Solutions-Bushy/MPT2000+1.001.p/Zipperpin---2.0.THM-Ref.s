%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2000+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xdWM9TpTOO

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 254 expanded)
%              Number of leaves         :   24 (  93 expanded)
%              Depth                    :    9
%              Number of atoms          :  929 (5029 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r1_waybel_3_type,type,(
    r1_waybel_3: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_waybel_7_type,type,(
    v5_waybel_7: $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_waybel_3_type,type,(
    v3_waybel_3: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k1_waybel_4_type,type,(
    k1_waybel_4: $i > $i )).

thf(t49_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_waybel_3 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v5_waybel_7 @ ( k1_waybel_4 @ A ) @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v4_waybel_7 @ B @ A )
             => ( v5_waybel_6 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v3_waybel_3 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( v5_waybel_7 @ ( k1_waybel_4 @ A ) @ A )
         => ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
             => ( ( v4_waybel_7 @ B @ A )
               => ( v5_waybel_6 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_waybel_7])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l57_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_waybel_3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v5_waybel_7 @ ( k1_waybel_4 @ A ) @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r1_waybel_3 @ A @ ( k12_lattice3 @ A @ C @ D ) @ B )
                          & ~ ( r3_orders_2 @ A @ C @ B )
                          & ~ ( r3_orders_2 @ A @ D @ B ) ) ) )
              & ~ ( v5_waybel_6 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_orders_2 @ X1 @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( v5_waybel_6 @ X0 @ X1 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X1 ) @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_waybel_3 @ X1 )
      | ~ ( v2_lattice3 @ X1 )
      | ~ ( v1_lattice3 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('2',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v3_waybel_3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A )
    | ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7','8','9','10','11'])).

thf('13',plain,(
    ~ ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( r1_waybel_3 @ X1 @ ( k12_lattice3 @ X1 @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( v5_waybel_6 @ X0 @ X1 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X1 ) @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_waybel_3 @ X1 )
      | ~ ( v2_lattice3 @ X1 )
      | ~ ( v1_lattice3 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('17',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v3_waybel_3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A )
    | ( v5_waybel_6 @ sk_B @ sk_A )
    | ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v5_waybel_6 @ sk_B @ sk_A )
    | ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19','20','21','22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v3_waybel_3 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v5_waybel_7 @ ( k1_waybel_4 @ A ) @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v4_waybel_7 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r1_waybel_3 @ A @ ( k12_lattice3 @ A @ C @ D ) @ B )
                          & ~ ( r3_orders_2 @ A @ C @ B )
                          & ~ ( r3_orders_2 @ A @ D @ B ) ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X2 ) @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ~ ( v4_waybel_7 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_waybel_3 @ X2 @ ( k12_lattice3 @ X2 @ X5 @ X4 ) @ X3 )
      | ( r3_orders_2 @ X2 @ X4 @ X3 )
      | ( r3_orders_2 @ X2 @ X5 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v3_waybel_3 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v1_yellow_0 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_waybel_7])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v3_waybel_3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ( r3_orders_2 @ sk_A @ X2 @ X1 )
      | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X0 @ X2 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_waybel_7 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ( r3_orders_2 @ sk_A @ X2 @ X1 )
      | ~ ( r1_waybel_3 @ sk_A @ ( k12_lattice3 @ sk_A @ X0 @ X2 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_waybel_7 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_waybel_7 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
    | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_waybel_7 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v5_waybel_6 @ X0 @ X1 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X1 ) @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_waybel_3 @ X1 )
      | ~ ( v2_lattice3 @ X1 )
      | ~ ( v1_lattice3 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v3_waybel_3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53','54','55','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,(
    ~ ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v5_waybel_6 @ X0 @ X1 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X1 ) @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_waybel_3 @ X1 )
      | ~ ( v2_lattice3 @ X1 )
      | ~ ( v1_lattice3 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v3_waybel_3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v5_waybel_6 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69','70','71','72'])).

thf('74',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','73'])).

thf('75',plain,(
    ~ ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
    | ( r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44','60','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r3_orders_2 @ X1 @ ( sk_D @ X0 @ X1 ) @ X0 )
      | ( v5_waybel_6 @ X0 @ X1 )
      | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ X1 ) @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_waybel_3 @ X1 )
      | ~ ( v2_lattice3 @ X1 )
      | ~ ( v1_lattice3 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l57_waybel_7])).

thf('80',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v3_waybel_3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A )
    | ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v3_waybel_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v5_waybel_7 @ ( k1_waybel_4 @ sk_A ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v5_waybel_6 @ sk_B @ sk_A )
    | ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86','87','88','89'])).

thf('91',plain,(
    ~ ( v5_waybel_6 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    r3_orders_2 @ sk_A @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['77','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['14','93'])).


%------------------------------------------------------------------------------
