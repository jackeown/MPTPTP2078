%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KUYHDStH1r

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  232 (1052 expanded)
%              Number of leaves         :   31 ( 316 expanded)
%              Depth                    :   18
%              Number of atoms          : 2080 (23128 expanded)
%              Number of equality atoms :  117 (1501 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t32_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v11_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( ( k4_lattices @ A @ B @ C )
                        = ( k4_lattices @ A @ B @ D ) )
                      & ( ( k3_lattices @ A @ B @ C )
                        = ( k3_lattices @ A @ B @ D ) ) )
                   => ( C = D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v11_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( ( k4_lattices @ A @ B @ C )
                          = ( k4_lattices @ A @ B @ D ) )
                        & ( ( k3_lattices @ A @ B @ C )
                          = ( k3_lattices @ A @ B @ D ) ) )
                     => ( C = D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_lattices])).

thf('0',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v11_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) )
                      = ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ ( k2_lattices @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v11_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ ( k1_lattices @ X4 @ X5 @ X7 ) )
        = ( k1_lattices @ X4 @ ( k2_lattices @ X4 @ X6 @ X5 ) @ ( k2_lattices @ X4 @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_2 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) )
      | ~ ( v11_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v11_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_2 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k4_lattices @ X16 @ X15 @ X17 )
        = ( k2_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('20',plain,(
    ! [X11: $i] :
      ( ( l1_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('21',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k1_lattices @ A @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l2_lattices @ X13 )
      | ~ ( v4_lattices @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k3_lattices @ X13 @ X12 @ X14 )
        = ( k1_lattices @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( l2_lattices @ X11 )
      | ~ ( l3_lattices @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('42',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','39','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_D_1 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','45'])).

thf('47',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k3_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('51',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('55',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('58',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('61',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k4_lattices @ A @ B @ B )
            = B ) ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( ( k4_lattices @ X19 @ X18 @ X18 )
        = X18 )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v9_lattices @ X19 )
      | ~ ( v8_lattices @ X19 )
      | ~ ( v6_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_lattices])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_C_2 )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['64','65','71','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_C_2 )
    = sk_C_2 ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_C_2
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['61','81'])).

thf('83',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['55','58','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v8_lattices @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k1_lattices @ X8 @ ( k2_lattices @ X8 @ X10 @ X9 ) @ X9 )
        = X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ sk_C_2 )
        = sk_C_2 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ sk_C_2 )
        = sk_C_2 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ sk_C_2 )
        = sk_C_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ sk_C_2 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k4_lattices @ X16 @ X15 @ X17 )
        = ( k2_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('99',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('106',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k4_lattices @ X2 @ X1 @ X3 )
        = ( k4_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('109',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('114',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['103','113'])).

thf('115',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['93','114'])).

thf('116',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['83','115'])).

thf('117',plain,
    ( sk_C_2
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['52','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_2 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k4_lattices @ X16 @ X15 @ X17 )
        = ( k2_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('127',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['122','130'])).

thf('132',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['104','112'])).

thf('134',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('137',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['134','137'])).

thf('139',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['131','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['118','142'])).

thf('144',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('145',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('147',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k4_lattices @ X2 @ X1 @ X3 )
        = ( k4_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('153',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['148','156'])).

thf('158',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['147','157'])).

thf('159',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['143','144','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('162',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('164',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('166',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( ( k4_lattices @ X19 @ X18 @ X18 )
        = X18 )
      | ~ ( l3_lattices @ X19 )
      | ~ ( v9_lattices @ X19 )
      | ~ ( v8_lattices @ X19 )
      | ~ ( v6_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_lattices])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('171',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('172',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('173',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
      = sk_D_1 ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
    = sk_D_1 ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,
    ( sk_D_1
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['166','176'])).

thf('178',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['162','163','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v8_lattices @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k1_lattices @ X8 @ ( k2_lattices @ X8 @ X10 @ X9 ) @ X9 )
        = X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_1 ) @ sk_D_1 )
        = sk_D_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_1 ) @ sk_D_1 )
        = sk_D_1 ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_1 ) @ sk_D_1 )
        = sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) @ sk_D_1 )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['179','187'])).

thf('189',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('191',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('193',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ sk_D_1 )
    = sk_D_1 ),
    inference(demod,[status(thm)],['188','193'])).

thf('195',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = sk_D_1 ),
    inference('sup+',[status(thm)],['178','194'])).

thf('196',plain,
    ( sk_D_1
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['159','195'])).

thf('197',plain,(
    sk_D_1 = sk_C_2 ),
    inference('sup+',[status(thm)],['117','196'])).

thf('198',plain,(
    sk_C_2 != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KUYHDStH1r
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:00:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 177 iterations in 0.095s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.54  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.21/0.54  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.21/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.54  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.21/0.54  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.21/0.54  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.21/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.54  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.21/0.54  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.21/0.54  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.21/0.54  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.21/0.54  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.21/0.54  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.21/0.54  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(t32_lattices, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.54         ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                   ( ( ( ( k4_lattices @ A @ B @ C ) =
% 0.21/0.54                         ( k4_lattices @ A @ B @ D ) ) & 
% 0.21/0.54                       ( ( k3_lattices @ A @ B @ C ) =
% 0.21/0.54                         ( k3_lattices @ A @ B @ D ) ) ) =>
% 0.21/0.54                     ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.21/0.54            ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                  ( ![D:$i]:
% 0.21/0.54                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                      ( ( ( ( k4_lattices @ A @ B @ C ) =
% 0.21/0.54                            ( k4_lattices @ A @ B @ D ) ) & 
% 0.21/0.54                          ( ( k3_lattices @ A @ B @ C ) =
% 0.21/0.54                            ( k3_lattices @ A @ B @ D ) ) ) =>
% 0.21/0.54                        ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t32_lattices])).
% 0.21/0.54  thf('0', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d11_lattices, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.54       ( ( v11_lattices @ A ) <=>
% 0.21/0.54         ( ![B:$i]:
% 0.21/0.54           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                 ( ![D:$i]:
% 0.21/0.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                     ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) ) =
% 0.21/0.54                       ( k1_lattices @
% 0.21/0.54                         A @ ( k2_lattices @ A @ B @ C ) @ 
% 0.21/0.54                         ( k2_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.54         (~ (v11_lattices @ X4)
% 0.21/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.54          | ((k2_lattices @ X4 @ X6 @ (k1_lattices @ X4 @ X5 @ X7))
% 0.21/0.54              = (k1_lattices @ X4 @ (k2_lattices @ X4 @ X6 @ X5) @ 
% 0.21/0.54                 (k2_lattices @ X4 @ X6 @ X7)))
% 0.21/0.54          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X4))
% 0.21/0.54          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.21/0.54          | ~ (l3_lattices @ X4)
% 0.21/0.54          | (v2_struct_0 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d11_lattices])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (l3_lattices @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ X1))
% 0.21/0.54              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ 
% 0.21/0.54                 (k2_lattices @ sk_A @ X0 @ X1)))
% 0.21/0.54          | ~ (v11_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf('5', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('6', plain, ((v11_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ X1))
% 0.21/0.54              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ 
% 0.21/0.54                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.54            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54               (k2_lattices @ sk_A @ sk_C_2 @ X0)))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.54  thf('9', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k4_lattices, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.54         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.54          | ~ (l1_lattices @ X16)
% 0.21/0.54          | ~ (v6_lattices @ X16)
% 0.21/0.54          | (v2_struct_0 @ X16)
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.54          | ((k4_lattices @ X16 @ X15 @ X17) = (k2_lattices @ X16 @ X15 @ X17)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.54            = (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v6_lattices @ sk_A)
% 0.21/0.54          | ~ (l1_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf(cc1_lattices, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l3_lattices @ A ) =>
% 0.21/0.54       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.21/0.54         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.54           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.21/0.54           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v10_lattices @ X0)
% 0.21/0.54          | (v6_lattices @ X0)
% 0.21/0.54          | ~ (l3_lattices @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.54  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain, ((v10_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('18', plain, ((v6_lattices @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.54  thf('19', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l3_lattices, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X11 : $i]: ((l1_lattices @ X11) | ~ (l3_lattices @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.54  thf('21', plain, ((l1_lattices @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.54            = (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['12', '18', '21'])).
% 0.21/0.54  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.54              = (k2_lattices @ sk_A @ sk_C_2 @ X0)))),
% 0.21/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.21/0.54         = (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.54            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54               (k2_lattices @ sk_A @ sk_C_2 @ X0)))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['8', '25'])).
% 0.21/0.54  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.54              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54                 (k2_lattices @ sk_A @ sk_C_2 @ X0))))),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))
% 0.21/0.54         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54            (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '28'])).
% 0.21/0.54  thf('30', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('31', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k3_lattices, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.21/0.54         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.21/0.54          | ~ (l2_lattices @ X13)
% 0.21/0.54          | ~ (v4_lattices @ X13)
% 0.21/0.54          | (v2_struct_0 @ X13)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.54          | ((k3_lattices @ X13 @ X12 @ X14) = (k1_lattices @ X13 @ X12 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.54            = (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v4_lattices @ sk_A)
% 0.21/0.54          | ~ (l2_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v10_lattices @ X0)
% 0.21/0.54          | (v4_lattices @ X0)
% 0.21/0.54          | ~ (l3_lattices @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.54  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain, ((v10_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain, ((v4_lattices @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.54  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X11 : $i]: ((l2_lattices @ X11) | ~ (l3_lattices @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.21/0.54  thf('42', plain, ((l2_lattices @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.54            = (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '39', '42'])).
% 0.21/0.54  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.54              = (k1_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.21/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (((k3_lattices @ sk_A @ sk_B_2 @ sk_D_1)
% 0.21/0.54         = (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.54         = (k3_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.54         = (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.54  thf('49', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.54              = (k2_lattices @ sk_A @ sk_C_2 @ X0)))),
% 0.21/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (((k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 0.21/0.54         = (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (((k2_lattices @ sk_A @ sk_C_2 @ (k3_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.54         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54            (k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['29', '48', '51'])).
% 0.21/0.54  thf('53', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.54              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54                 (k2_lattices @ sk_A @ sk_C_2 @ X0))))),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.54         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54            (k2_lattices @ sk_A @ sk_C_2 @ sk_C_2)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.54              = (k1_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.21/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.54         = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.54              = (k2_lattices @ sk_A @ sk_C_2 @ X0)))),
% 0.21/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (((k4_lattices @ sk_A @ sk_C_2 @ sk_C_2)
% 0.21/0.54         = (k2_lattices @ sk_A @ sk_C_2 @ sk_C_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.54  thf('62', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t18_lattices, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.54         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ( k4_lattices @ A @ B @ B ) = ( B ) ) ) ) ))).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.54          | ((k4_lattices @ X19 @ X18 @ X18) = (X18))
% 0.21/0.54          | ~ (l3_lattices @ X19)
% 0.21/0.54          | ~ (v9_lattices @ X19)
% 0.21/0.54          | ~ (v8_lattices @ X19)
% 0.21/0.54          | ~ (v6_lattices @ X19)
% 0.21/0.54          | (v2_struct_0 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t18_lattices])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v6_lattices @ sk_A)
% 0.21/0.54        | ~ (v8_lattices @ sk_A)
% 0.21/0.54        | ~ (v9_lattices @ sk_A)
% 0.21/0.54        | ~ (l3_lattices @ sk_A)
% 0.21/0.54        | ((k4_lattices @ sk_A @ sk_C_2 @ sk_C_2) = (sk_C_2)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('65', plain, ((v6_lattices @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v10_lattices @ X0)
% 0.21/0.54          | (v8_lattices @ X0)
% 0.21/0.54          | ~ (l3_lattices @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.54  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.54  thf('69', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('70', plain, ((v10_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('71', plain, ((v8_lattices @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X0)
% 0.21/0.54          | ~ (v10_lattices @ X0)
% 0.21/0.54          | (v9_lattices @ X0)
% 0.21/0.54          | ~ (l3_lattices @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.21/0.54  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('76', plain, ((v10_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('77', plain, ((v9_lattices @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.54  thf('78', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ((k4_lattices @ sk_A @ sk_C_2 @ sk_C_2) = (sk_C_2)))),
% 0.21/0.54      inference('demod', [status(thm)], ['64', '65', '71', '77', '78'])).
% 0.21/0.54  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('81', plain, (((k4_lattices @ sk_A @ sk_C_2 @ sk_C_2) = (sk_C_2))),
% 0.21/0.54      inference('clc', [status(thm)], ['79', '80'])).
% 0.21/0.54  thf('82', plain, (((sk_C_2) = (k2_lattices @ sk_A @ sk_C_2 @ sk_C_2))),
% 0.21/0.54      inference('demod', [status(thm)], ['61', '81'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (((k2_lattices @ sk_A @ sk_C_2 @ (k3_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.54         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.54            sk_C_2))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '58', '82'])).
% 0.21/0.54  thf('84', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('85', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d8_lattices, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.21/0.54       ( ( v8_lattices @ A ) <=>
% 0.21/0.54         ( ![B:$i]:
% 0.21/0.54           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.21/0.54                   ( C ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (v8_lattices @ X8)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.54          | ((k1_lattices @ X8 @ (k2_lattices @ X8 @ X10 @ X9) @ X9) = (X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.54          | ~ (l3_lattices @ X8)
% 0.21/0.54          | (v2_struct_0 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_lattices])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (l3_lattices @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_2) @ sk_C_2)
% 0.21/0.54              = (sk_C_2))
% 0.21/0.54          | ~ (v8_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.54  thf('88', plain, ((l3_lattices @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('89', plain, ((v8_lattices @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_2) @ sk_C_2)
% 0.21/0.54              = (sk_C_2)))),
% 0.21/0.54      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.21/0.54  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_2) @ sk_C_2)
% 0.21/0.54            = (sk_C_2))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['90', '91'])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ sk_C_2)
% 0.21/0.54         = (sk_C_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['84', '92'])).
% 0.21/0.54  thf('94', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('95', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.54          | ~ (l1_lattices @ X16)
% 0.21/0.54          | ~ (v6_lattices @ X16)
% 0.21/0.54          | (v2_struct_0 @ X16)
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.54          | ((k4_lattices @ X16 @ X15 @ X17) = (k2_lattices @ X16 @ X15 @ X17)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.21/0.54  thf('97', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.54            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v6_lattices @ sk_A)
% 0.21/0.54          | ~ (l1_lattices @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.54  thf('98', plain, ((v6_lattices @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.54  thf('99', plain, ((l1_lattices @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.55         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.55            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.21/0.55  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('102', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.55              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.21/0.55      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.55  thf('103', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['94', '102'])).
% 0.21/0.55  thf('104', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('105', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(commutativity_k4_lattices, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.21/0.55         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.21/0.55  thf('106', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.55          | ~ (l1_lattices @ X2)
% 0.21/0.55          | ~ (v6_lattices @ X2)
% 0.21/0.55          | (v2_struct_0 @ X2)
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.55          | ((k4_lattices @ X2 @ X1 @ X3) = (k4_lattices @ X2 @ X3 @ X1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.21/0.55  thf('107', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.55            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v6_lattices @ sk_A)
% 0.21/0.55          | ~ (l1_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.55  thf('108', plain, ((v6_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.55  thf('109', plain, ((l1_lattices @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('110', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.55            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.21/0.55  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('112', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.55              = (k4_lattices @ sk_A @ X0 @ sk_B_2)))),
% 0.21/0.55      inference('clc', [status(thm)], ['110', '111'])).
% 0.21/0.55  thf('113', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['104', '112'])).
% 0.21/0.55  thf('114', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 0.21/0.55      inference('demod', [status(thm)], ['103', '113'])).
% 0.21/0.55  thf('115', plain,
% 0.21/0.55      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ sk_C_2)
% 0.21/0.55         = (sk_C_2))),
% 0.21/0.55      inference('demod', [status(thm)], ['93', '114'])).
% 0.21/0.55  thf('116', plain,
% 0.21/0.55      (((k2_lattices @ sk_A @ sk_C_2 @ (k3_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.55         = (sk_C_2))),
% 0.21/0.55      inference('sup+', [status(thm)], ['83', '115'])).
% 0.21/0.55  thf('117', plain,
% 0.21/0.55      (((sk_C_2)
% 0.21/0.55         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55            (k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['52', '116'])).
% 0.21/0.55  thf('118', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('119', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('120', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ X1))
% 0.21/0.55              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ 
% 0.21/0.55                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.55  thf('121', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.55            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_D_1 @ sk_B_2) @ 
% 0.21/0.55               (k2_lattices @ sk_A @ sk_D_1 @ X0)))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['119', '120'])).
% 0.21/0.55  thf('122', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('123', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('124', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.21/0.55          | ~ (l1_lattices @ X16)
% 0.21/0.55          | ~ (v6_lattices @ X16)
% 0.21/0.55          | (v2_struct_0 @ X16)
% 0.21/0.55          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.55          | ((k4_lattices @ X16 @ X15 @ X17) = (k2_lattices @ X16 @ X15 @ X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.21/0.55  thf('125', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.21/0.55            = (k2_lattices @ sk_A @ sk_D_1 @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v6_lattices @ sk_A)
% 0.21/0.55          | ~ (l1_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['123', '124'])).
% 0.21/0.55  thf('126', plain, ((v6_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.55  thf('127', plain, ((l1_lattices @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('128', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.21/0.55            = (k2_lattices @ sk_A @ sk_D_1 @ X0))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.21/0.55  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('130', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.21/0.55              = (k2_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.21/0.55      inference('clc', [status(thm)], ['128', '129'])).
% 0.21/0.55  thf('131', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_D_1 @ sk_B_2)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['122', '130'])).
% 0.21/0.55  thf('132', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('133', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['104', '112'])).
% 0.21/0.55  thf('134', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['132', '133'])).
% 0.21/0.55  thf('135', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('136', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.55              = (k4_lattices @ sk_A @ X0 @ sk_B_2)))),
% 0.21/0.55      inference('clc', [status(thm)], ['110', '111'])).
% 0.21/0.55  thf('137', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_B_2 @ sk_D_1)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['135', '136'])).
% 0.21/0.55  thf('138', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.21/0.55      inference('sup+', [status(thm)], ['134', '137'])).
% 0.21/0.55  thf('139', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.21/0.55      inference('demod', [status(thm)], ['131', '138'])).
% 0.21/0.55  thf('140', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.55            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55               (k2_lattices @ sk_A @ sk_D_1 @ X0)))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['121', '139'])).
% 0.21/0.55  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('142', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.55              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55                 (k2_lattices @ sk_A @ sk_D_1 @ X0))))),
% 0.21/0.55      inference('clc', [status(thm)], ['140', '141'])).
% 0.21/0.55  thf('143', plain,
% 0.21/0.55      (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.55         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55            (k2_lattices @ sk_A @ sk_D_1 @ sk_C_2)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['118', '142'])).
% 0.21/0.55  thf('144', plain,
% 0.21/0.55      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.55         = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.55  thf('145', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('146', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.21/0.55              = (k2_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.21/0.55      inference('clc', [status(thm)], ['128', '129'])).
% 0.21/0.55  thf('147', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_D_1 @ sk_C_2)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_D_1 @ sk_C_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['145', '146'])).
% 0.21/0.55  thf('148', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('149', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('150', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.55          | ~ (l1_lattices @ X2)
% 0.21/0.55          | ~ (v6_lattices @ X2)
% 0.21/0.55          | (v2_struct_0 @ X2)
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.21/0.55          | ((k4_lattices @ X2 @ X1 @ X3) = (k4_lattices @ X2 @ X3 @ X1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.21/0.55  thf('151', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.55            = (k4_lattices @ sk_A @ X0 @ sk_C_2))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v6_lattices @ sk_A)
% 0.21/0.55          | ~ (l1_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['149', '150'])).
% 0.21/0.55  thf('152', plain, ((v6_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.55  thf('153', plain, ((l1_lattices @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('154', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.55            = (k4_lattices @ sk_A @ X0 @ sk_C_2))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.21/0.55  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('156', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.21/0.55              = (k4_lattices @ sk_A @ X0 @ sk_C_2)))),
% 0.21/0.55      inference('clc', [status(thm)], ['154', '155'])).
% 0.21/0.55  thf('157', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_D_1 @ sk_C_2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['148', '156'])).
% 0.21/0.55  thf('158', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_D_1 @ sk_C_2))),
% 0.21/0.55      inference('demod', [status(thm)], ['147', '157'])).
% 0.21/0.55  thf('159', plain,
% 0.21/0.55      (((k2_lattices @ sk_A @ sk_D_1 @ (k3_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.55         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55            (k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['143', '144', '158'])).
% 0.21/0.55  thf('160', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('161', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.21/0.55              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55                 (k2_lattices @ sk_A @ sk_D_1 @ X0))))),
% 0.21/0.55      inference('clc', [status(thm)], ['140', '141'])).
% 0.21/0.55  thf('162', plain,
% 0.21/0.55      (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))
% 0.21/0.55         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55            (k2_lattices @ sk_A @ sk_D_1 @ sk_D_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['160', '161'])).
% 0.21/0.55  thf('163', plain,
% 0.21/0.55      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.21/0.55         = (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf('164', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('165', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.21/0.55              = (k2_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.21/0.55      inference('clc', [status(thm)], ['128', '129'])).
% 0.21/0.55  thf('166', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_D_1 @ sk_D_1)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_D_1 @ sk_D_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['164', '165'])).
% 0.21/0.55  thf('167', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('168', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.55          | ((k4_lattices @ X19 @ X18 @ X18) = (X18))
% 0.21/0.55          | ~ (l3_lattices @ X19)
% 0.21/0.55          | ~ (v9_lattices @ X19)
% 0.21/0.55          | ~ (v8_lattices @ X19)
% 0.21/0.55          | ~ (v6_lattices @ X19)
% 0.21/0.55          | (v2_struct_0 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t18_lattices])).
% 0.21/0.55  thf('169', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v6_lattices @ sk_A)
% 0.21/0.55        | ~ (v8_lattices @ sk_A)
% 0.21/0.55        | ~ (v9_lattices @ sk_A)
% 0.21/0.55        | ~ (l3_lattices @ sk_A)
% 0.21/0.55        | ((k4_lattices @ sk_A @ sk_D_1 @ sk_D_1) = (sk_D_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['167', '168'])).
% 0.21/0.55  thf('170', plain, ((v6_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.55  thf('171', plain, ((v8_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.55  thf('172', plain, ((v9_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.55  thf('173', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('174', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((k4_lattices @ sk_A @ sk_D_1 @ sk_D_1) = (sk_D_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 0.21/0.55  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('176', plain, (((k4_lattices @ sk_A @ sk_D_1 @ sk_D_1) = (sk_D_1))),
% 0.21/0.55      inference('clc', [status(thm)], ['174', '175'])).
% 0.21/0.55  thf('177', plain, (((sk_D_1) = (k2_lattices @ sk_A @ sk_D_1 @ sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['166', '176'])).
% 0.21/0.55  thf('178', plain,
% 0.21/0.55      (((k2_lattices @ sk_A @ sk_D_1 @ (k3_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.55         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55            sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['162', '163', '177'])).
% 0.21/0.55  thf('179', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('180', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('181', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.55         (~ (v8_lattices @ X8)
% 0.21/0.55          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.55          | ((k1_lattices @ X8 @ (k2_lattices @ X8 @ X10 @ X9) @ X9) = (X9))
% 0.21/0.55          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.55          | ~ (l3_lattices @ X8)
% 0.21/0.55          | (v2_struct_0 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [d8_lattices])).
% 0.21/0.55  thf('182', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (l3_lattices @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_1) @ sk_D_1)
% 0.21/0.55              = (sk_D_1))
% 0.21/0.55          | ~ (v8_lattices @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['180', '181'])).
% 0.21/0.55  thf('183', plain, ((l3_lattices @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('184', plain, ((v8_lattices @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.55  thf('185', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_1) @ sk_D_1)
% 0.21/0.55              = (sk_D_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['182', '183', '184'])).
% 0.21/0.55  thf('186', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('187', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_1) @ sk_D_1)
% 0.21/0.55            = (sk_D_1))
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['185', '186'])).
% 0.21/0.55  thf('188', plain,
% 0.21/0.55      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_D_1) @ sk_D_1)
% 0.21/0.55         = (sk_D_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['179', '187'])).
% 0.21/0.55  thf('189', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('190', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.21/0.55              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.21/0.55      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.55  thf('191', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_B_2 @ sk_D_1)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['189', '190'])).
% 0.21/0.55  thf('192', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.21/0.55         = (k4_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['132', '133'])).
% 0.21/0.55  thf('193', plain,
% 0.21/0.55      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.21/0.55         = (k2_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['191', '192'])).
% 0.21/0.55  thf('194', plain,
% 0.21/0.55      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ sk_D_1)
% 0.21/0.55         = (sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['188', '193'])).
% 0.21/0.55  thf('195', plain,
% 0.21/0.55      (((k2_lattices @ sk_A @ sk_D_1 @ (k3_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.21/0.55         = (sk_D_1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['178', '194'])).
% 0.21/0.55  thf('196', plain,
% 0.21/0.55      (((sk_D_1)
% 0.21/0.55         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.21/0.55            (k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['159', '195'])).
% 0.21/0.55  thf('197', plain, (((sk_D_1) = (sk_C_2))),
% 0.21/0.55      inference('sup+', [status(thm)], ['117', '196'])).
% 0.21/0.55  thf('198', plain, (((sk_C_2) != (sk_D_1))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('199', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['197', '198'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
