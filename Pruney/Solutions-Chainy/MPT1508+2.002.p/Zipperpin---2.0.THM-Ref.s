%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WO3PegW3rI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 209 expanded)
%              Number of leaves         :   26 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  814 (3131 expanded)
%              Number of equality atoms :   19 ( 113 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t42_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r3_lattice3 @ A @ B @ C ) )
             => ( ( k16_lattice3 @ A @ C )
                = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ( r2_hidden @ B @ C )
                  & ( r3_lattice3 @ A @ B @ C ) )
               => ( ( k16_lattice3 @ A @ C )
                  = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( B
                = ( k16_lattice3 @ A @ C ) )
            <=> ( ( r3_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r3_lattice3 @ A @ D @ C )
                     => ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r3_lattice3 @ X10 @ X9 @ X13 )
      | ( r3_lattice3 @ X10 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X13 )
      | ( X9
        = ( k16_lattice3 @ X10 @ X13 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( r3_lattice3 @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r3_lattice3 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r3_lattice3 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r3_lattice3 @ X10 @ X9 @ X13 )
      | ( m1_subset_1 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( X9
        = ( k16_lattice3 @ X10 @ X13 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d16_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r3_lattice3 @ X5 @ X4 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_lattices @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r3_lattice3 @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l3_lattices @ X2 )
      | ~ ( v9_lattices @ X2 )
      | ~ ( v8_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r3_lattices @ X2 @ X1 @ X3 )
      | ~ ( r1_lattices @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ( r3_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','46','52','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r3_lattices @ sk_A @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r3_lattice3 @ X10 @ X9 @ X13 )
      | ~ ( r3_lattices @ X10 @ ( sk_D_1 @ X13 @ X9 @ X10 ) @ X9 )
      | ( X9
        = ( k16_lattice3 @ X10 @ X13 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v4_lattice3 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t34_lattice3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( k16_lattice3 @ sk_A @ X0 ) )
      | ~ ( r3_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r3_lattice3 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ~ ( r3_lattice3 @ sk_A @ sk_B @ sk_C )
    | ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    r3_lattice3 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_B
      = ( k16_lattice3 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k16_lattice3 @ sk_A @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WO3PegW3rI
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:02:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 74 iterations in 0.074s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.53  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.53  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.53  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.21/0.53  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.53  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.21/0.53  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.21/0.53  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.53  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.53  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(t42_lattice3, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.53               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.21/0.53                  ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t42_lattice3])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t34_lattice3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.53         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( B ) = ( k16_lattice3 @ A @ C ) ) <=>
% 0.21/0.53               ( ( r3_lattice3 @ A @ B @ C ) & 
% 0.21/0.53                 ( ![D:$i]:
% 0.21/0.53                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                     ( ( r3_lattice3 @ A @ D @ C ) =>
% 0.21/0.53                       ( r3_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ~ (r3_lattice3 @ X10 @ X9 @ X13)
% 0.21/0.53          | (r3_lattice3 @ X10 @ (sk_D_1 @ X13 @ X9 @ X10) @ X13)
% 0.21/0.53          | ((X9) = (k16_lattice3 @ X10 @ X13))
% 0.21/0.53          | ~ (l3_lattices @ X10)
% 0.21/0.53          | ~ (v4_lattice3 @ X10)
% 0.21/0.53          | ~ (v10_lattices @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v10_lattices @ sk_A)
% 0.21/0.53          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('8', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | (r3_lattice3 @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (((r3_lattice3 @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.53        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.53  thf('11', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (((r3_lattice3 @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((r3_lattice3 @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.53      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ~ (r3_lattice3 @ X10 @ X9 @ X13)
% 0.21/0.53          | (m1_subset_1 @ (sk_D_1 @ X13 @ X9 @ X10) @ (u1_struct_0 @ X10))
% 0.21/0.53          | ((X9) = (k16_lattice3 @ X10 @ X13))
% 0.21/0.53          | ~ (l3_lattices @ X10)
% 0.21/0.53          | ~ (v4_lattice3 @ X10)
% 0.21/0.53          | ~ (v10_lattices @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v10_lattices @ sk_A)
% 0.21/0.53          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('21', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '22'])).
% 0.21/0.53  thf('24', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf(d16_lattice3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.21/0.53          | ~ (r3_lattice3 @ X5 @ X4 @ X6)
% 0.21/0.53          | ~ (r2_hidden @ X7 @ X6)
% 0.21/0.53          | (r1_lattices @ X5 @ X4 @ X7)
% 0.21/0.53          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.21/0.53          | ~ (l3_lattices @ X5)
% 0.21/0.53          | (v2_struct_0 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ sk_C)
% 0.21/0.53          | (r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.53        | ~ (r2_hidden @ sk_B @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '32'])).
% 0.21/0.53  thf('34', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf(redefinition_r3_lattices, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.53         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.21/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.53          | ~ (l3_lattices @ X2)
% 0.21/0.53          | ~ (v9_lattices @ X2)
% 0.21/0.53          | ~ (v8_lattices @ X2)
% 0.21/0.53          | ~ (v6_lattices @ X2)
% 0.21/0.53          | (v2_struct_0 @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.53          | (r3_lattices @ X2 @ X1 @ X3)
% 0.21/0.53          | ~ (r1_lattices @ X2 @ X1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | (r3_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v6_lattices @ sk_A)
% 0.21/0.53          | ~ (v8_lattices @ sk_A)
% 0.21/0.53          | ~ (v9_lattices @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf(cc1_lattices, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l3_lattices @ A ) =>
% 0.21/0.53       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.53         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.53           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.53           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v6_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('45', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain, ((v6_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v8_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain, ((v8_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (v10_lattices @ X0)
% 0.21/0.53          | (v9_lattices @ X0)
% 0.21/0.53          | ~ (l3_lattices @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.53  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain, ((v9_lattices @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.53  thf('59', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | (r3_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['40', '46', '52', '58', '59'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (r3_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '60'])).
% 0.21/0.53  thf('62', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (r3_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((r3_lattices @ sk_A @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.53  thf('66', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.53          | ~ (r3_lattice3 @ X10 @ X9 @ X13)
% 0.21/0.53          | ~ (r3_lattices @ X10 @ (sk_D_1 @ X13 @ X9 @ X10) @ X9)
% 0.21/0.53          | ((X9) = (k16_lattice3 @ X10 @ X13))
% 0.21/0.53          | ~ (l3_lattices @ X10)
% 0.21/0.53          | ~ (v4_lattice3 @ X10)
% 0.21/0.53          | ~ (v10_lattices @ X10)
% 0.21/0.53          | (v2_struct_0 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t34_lattice3])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v10_lattices @ sk_A)
% 0.21/0.53          | ~ (v4_lattice3 @ sk_A)
% 0.21/0.53          | ~ (l3_lattices @ sk_A)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | ~ (r3_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.53  thf('69', plain, ((v10_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain, ((v4_lattice3 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain, ((l3_lattices @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ((sk_B) = (k16_lattice3 @ sk_A @ X0))
% 0.21/0.53          | ~ (r3_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.53          | ~ (r3_lattice3 @ sk_A @ sk_B @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((~ (r3_lattice3 @ sk_A @ sk_B @ sk_C)
% 0.21/0.53        | ((sk_B) = (k16_lattice3 @ sk_A @ sk_C))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '72'])).
% 0.21/0.53  thf('74', plain, ((r3_lattice3 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      ((((sk_B) = (k16_lattice3 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.53  thf('76', plain, (((k16_lattice3 @ sk_A @ sk_C) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('77', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.21/0.53  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
