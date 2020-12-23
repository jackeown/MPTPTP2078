%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aho1yXiND9

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:32 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  247 (1046 expanded)
%              Number of leaves         :   32 ( 314 expanded)
%              Depth                    :   18
%              Number of atoms          : 2237 (23104 expanded)
%              Number of equality atoms :  124 (1501 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v11_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( ( k2_lattices @ X6 @ X8 @ ( k1_lattices @ X6 @ X7 @ X9 ) )
        = ( k1_lattices @ X6 @ ( k2_lattices @ X6 @ X8 @ X7 ) @ ( k2_lattices @ X6 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d11_lattices])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) )
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
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_lattices @ X21 )
      | ~ ( v6_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( ( k4_lattices @ X21 @ X20 @ X22 )
        = ( k2_lattices @ X21 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) )
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
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v6_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
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
    ! [X16: $i] :
      ( ( l1_lattices @ X16 )
      | ~ ( l3_lattices @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('21',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l2_lattices @ X18 )
      | ~ ( v4_lattices @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( ( k3_lattices @ X18 @ X17 @ X19 )
        = ( k1_lattices @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v4_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
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
    ! [X16: $i] :
      ( ( l2_lattices @ X16 )
      | ~ ( l3_lattices @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('42',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','39','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_D_1 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','45'])).

thf('47',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k3_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('51',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('55',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('58',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v9_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k2_lattices @ X13 @ X15 @ ( k1_lattices @ X13 @ X15 @ X14 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_3 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v9_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_3 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','63','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_C_3 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) )
    = sk_C_3 ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('75',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( k1_lattices @ X24 @ X23 @ X23 )
        = X23 )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v9_lattices @ X24 )
      | ~ ( v8_lattices @ X24 )
      | ~ ( v6_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t17_lattices])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
      = sk_C_3 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('78',plain,(
    ! [X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v10_lattices @ X2 )
      | ( v8_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('85',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
      = sk_C_3 ) ),
    inference(demod,[status(thm)],['76','77','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = sk_C_3 ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = sk_C_3 ),
    inference(demod,[status(thm)],['73','88'])).

thf('90',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_C_3 ) ),
    inference(demod,[status(thm)],['55','58','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('93',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v8_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k1_lattices @ X10 @ ( k2_lattices @ X10 @ X12 @ X11 ) @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ sk_C_3 )
        = sk_C_3 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ sk_C_3 )
        = sk_C_3 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ sk_C_3 )
        = sk_C_3 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) @ sk_C_3 )
    = sk_C_3 ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_lattices @ X21 )
      | ~ ( v6_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( ( k4_lattices @ X21 @ X20 @ X22 )
        = ( k2_lattices @ X21 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('106',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('113',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ~ ( v6_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k4_lattices @ X4 @ X3 @ X5 )
        = ( k4_lattices @ X4 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('116',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('121',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['110','120'])).

thf('122',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_C_3 )
    = sk_C_3 ),
    inference(demod,[status(thm)],['100','121'])).

thf('123',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = sk_C_3 ),
    inference('sup+',[status(thm)],['90','122'])).

thf('124',plain,
    ( sk_C_3
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['52','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_lattices @ X21 )
      | ~ ( v6_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( ( k4_lattices @ X21 @ X20 @ X22 )
        = ( k2_lattices @ X21 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('134',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['129','137'])).

thf('139',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['111','119'])).

thf('141',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('144',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_1 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['141','144'])).

thf('146',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['138','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['125','149'])).

thf('151',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('152',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('154',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_C_3 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ~ ( v6_lattices @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k4_lattices @ X4 @ X3 @ X5 )
        = ( k4_lattices @ X4 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('160',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_3 ) ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_1 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('165',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['154','164'])).

thf('166',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['150','151','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('169',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('171',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v9_lattices @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k2_lattices @ X13 @ X15 @ ( k1_lattices @ X13 @ X15 @ X14 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_D_1 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_D_1 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_D_1 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_D_1 @ sk_D_1 ) )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['171','179'])).

thf('181',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( k1_lattices @ X24 @ X23 @ X23 )
        = X23 )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v9_lattices @ X24 )
      | ~ ( v8_lattices @ X24 )
      | ~ ( v6_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t17_lattices])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('185',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('186',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('187',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
      = sk_D_1 ) ),
    inference(demod,[status(thm)],['183','184','185','186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k1_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
    = sk_D_1 ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ sk_D_1 )
    = sk_D_1 ),
    inference(demod,[status(thm)],['180','190'])).

thf('192',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['169','170','191'])).

thf('193',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v8_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k1_lattices @ X10 @ ( k2_lattices @ X10 @ X12 @ X11 ) @ X11 )
        = X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_1 ) @ sk_D_1 )
        = sk_D_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_1 ) @ sk_D_1 )
        = sk_D_1 ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_1 ) @ sk_D_1 )
        = sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) @ sk_D_1 )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['193','201'])).

thf('203',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('205',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('207',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_D_1 )
    = sk_D_1 ),
    inference(demod,[status(thm)],['202','207'])).

thf('209',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = sk_D_1 ),
    inference('sup+',[status(thm)],['192','208'])).

thf('210',plain,
    ( sk_D_1
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['166','209'])).

thf('211',plain,(
    sk_D_1 = sk_C_3 ),
    inference('sup+',[status(thm)],['124','210'])).

thf('212',plain,(
    sk_C_3 != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['211','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aho1yXiND9
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:44:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 213 iterations in 0.168s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.62  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.43/0.62  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.43/0.62  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.43/0.62  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.43/0.62  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.43/0.62  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 0.43/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.62  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.43/0.62  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.43/0.62  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.43/0.62  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.43/0.62  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.43/0.62  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.43/0.62  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.43/0.62  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.43/0.62  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.43/0.62  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.43/0.62  thf(t32_lattices, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.62         ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62               ( ![D:$i]:
% 0.43/0.62                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62                   ( ( ( ( k4_lattices @ A @ B @ C ) =
% 0.43/0.62                         ( k4_lattices @ A @ B @ D ) ) & 
% 0.43/0.62                       ( ( k3_lattices @ A @ B @ C ) =
% 0.43/0.62                         ( k3_lattices @ A @ B @ D ) ) ) =>
% 0.43/0.62                     ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.43/0.62            ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62              ( ![C:$i]:
% 0.43/0.62                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62                  ( ![D:$i]:
% 0.43/0.62                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62                      ( ( ( ( k4_lattices @ A @ B @ C ) =
% 0.43/0.62                            ( k4_lattices @ A @ B @ D ) ) & 
% 0.43/0.62                          ( ( k3_lattices @ A @ B @ C ) =
% 0.43/0.62                            ( k3_lattices @ A @ B @ D ) ) ) =>
% 0.43/0.62                        ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t32_lattices])).
% 0.43/0.62  thf('0', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('2', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d11_lattices, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.62       ( ( v11_lattices @ A ) <=>
% 0.43/0.62         ( ![B:$i]:
% 0.43/0.62           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62             ( ![C:$i]:
% 0.43/0.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62                 ( ![D:$i]:
% 0.43/0.62                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62                     ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) ) =
% 0.43/0.62                       ( k1_lattices @
% 0.43/0.62                         A @ ( k2_lattices @ A @ B @ C ) @ 
% 0.43/0.62                         ( k2_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         (~ (v11_lattices @ X6)
% 0.43/0.62          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.43/0.62          | ((k2_lattices @ X6 @ X8 @ (k1_lattices @ X6 @ X7 @ X9))
% 0.43/0.62              = (k1_lattices @ X6 @ (k2_lattices @ X6 @ X8 @ X7) @ 
% 0.43/0.62                 (k2_lattices @ X6 @ X8 @ X9)))
% 0.43/0.62          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X6))
% 0.43/0.62          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.43/0.62          | ~ (l3_lattices @ X6)
% 0.43/0.62          | (v2_struct_0 @ X6))),
% 0.43/0.62      inference('cnf', [status(esa)], [d11_lattices])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((v2_struct_0 @ sk_A)
% 0.43/0.62          | ~ (l3_lattices @ sk_A)
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.43/0.62          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_3 @ X1))
% 0.43/0.62              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ 
% 0.43/0.62                 (k2_lattices @ sk_A @ X0 @ X1)))
% 0.43/0.62          | ~ (v11_lattices @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain, ((l3_lattices @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('6', plain, ((v11_lattices @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((v2_struct_0 @ sk_A)
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.43/0.62          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_3 @ X1))
% 0.43/0.62              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ 
% 0.43/0.62                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.62            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.62               (k2_lattices @ sk_A @ sk_C_3 @ X0)))
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '7'])).
% 0.43/0.62  thf('9', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('10', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(redefinition_k4_lattices, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.43/0.62         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.43/0.62         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.43/0.62          | ~ (l1_lattices @ X21)
% 0.43/0.62          | ~ (v6_lattices @ X21)
% 0.43/0.62          | (v2_struct_0 @ X21)
% 0.43/0.62          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.43/0.62          | ((k4_lattices @ X21 @ X20 @ X22) = (k2_lattices @ X21 @ X20 @ X22)))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 0.43/0.62            = (k2_lattices @ sk_A @ sk_C_3 @ X0))
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62          | (v2_struct_0 @ sk_A)
% 0.43/0.62          | ~ (v6_lattices @ sk_A)
% 0.43/0.62          | ~ (l1_lattices @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf(cc1_lattices, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l3_lattices @ A ) =>
% 0.43/0.62       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.43/0.62         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.43/0.62           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.43/0.62           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X2 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X2)
% 0.43/0.62          | ~ (v10_lattices @ X2)
% 0.43/0.62          | (v6_lattices @ X2)
% 0.43/0.62          | ~ (l3_lattices @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.43/0.62  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf('16', plain, ((l3_lattices @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('17', plain, ((v10_lattices @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('18', plain, ((v6_lattices @ sk_A)),
% 0.43/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.43/0.63  thf('19', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(dt_l3_lattices, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.43/0.63  thf('20', plain,
% 0.43/0.63      (![X16 : $i]: ((l1_lattices @ X16) | ~ (l3_lattices @ X16))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.43/0.63  thf('21', plain, ((l1_lattices @ sk_A)),
% 0.43/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 0.43/0.63            = (k2_lattices @ sk_A @ sk_C_3 @ X0))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['12', '18', '21'])).
% 0.43/0.63  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('24', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 0.43/0.63              = (k2_lattices @ sk_A @ sk_C_3 @ X0)))),
% 0.43/0.63      inference('clc', [status(thm)], ['22', '23'])).
% 0.43/0.63  thf('25', plain,
% 0.43/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 0.43/0.63         = (k2_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 0.43/0.63      inference('sup-', [status(thm)], ['9', '24'])).
% 0.43/0.63  thf('26', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.63            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63               (k2_lattices @ sk_A @ sk_C_3 @ X0)))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['8', '25'])).
% 0.43/0.63  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('28', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.63              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63                 (k2_lattices @ sk_A @ sk_C_3 @ X0))))),
% 0.43/0.63      inference('clc', [status(thm)], ['26', '27'])).
% 0.43/0.63  thf('29', plain,
% 0.43/0.63      (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ sk_D_1))
% 0.43/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63            (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['0', '28'])).
% 0.43/0.63  thf('30', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('31', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(redefinition_k3_lattices, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.43/0.63         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.43/0.63         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.43/0.63  thf('32', plain,
% 0.43/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.43/0.63          | ~ (l2_lattices @ X18)
% 0.43/0.63          | ~ (v4_lattices @ X18)
% 0.43/0.63          | (v2_struct_0 @ X18)
% 0.43/0.63          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.43/0.63          | ((k3_lattices @ X18 @ X17 @ X19) = (k1_lattices @ X18 @ X17 @ X19)))),
% 0.43/0.63      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.43/0.63  thf('33', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63            = (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (v4_lattices @ sk_A)
% 0.43/0.63          | ~ (l2_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.63  thf('34', plain,
% 0.43/0.63      (![X2 : $i]:
% 0.43/0.63         ((v2_struct_0 @ X2)
% 0.43/0.63          | ~ (v10_lattices @ X2)
% 0.43/0.63          | (v4_lattices @ X2)
% 0.43/0.63          | ~ (l3_lattices @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.43/0.63  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('36', plain,
% 0.43/0.63      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.63  thf('37', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('38', plain, ((v10_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('39', plain, ((v4_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.43/0.63  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('41', plain,
% 0.43/0.63      (![X16 : $i]: ((l2_lattices @ X16) | ~ (l3_lattices @ X16))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.43/0.63  thf('42', plain, ((l2_lattices @ sk_A)),
% 0.43/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.63  thf('43', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63            = (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['33', '39', '42'])).
% 0.43/0.63  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('45', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63              = (k1_lattices @ sk_A @ sk_B_3 @ X0)))),
% 0.43/0.63      inference('clc', [status(thm)], ['43', '44'])).
% 0.43/0.63  thf('46', plain,
% 0.43/0.63      (((k3_lattices @ sk_A @ sk_B_3 @ sk_D_1)
% 0.43/0.63         = (k1_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.43/0.63      inference('sup-', [status(thm)], ['30', '45'])).
% 0.43/0.63  thf('47', plain,
% 0.43/0.63      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.43/0.63         = (k3_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('48', plain,
% 0.43/0.63      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.43/0.63         = (k1_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.43/0.63      inference('demod', [status(thm)], ['46', '47'])).
% 0.43/0.63  thf('49', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('50', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 0.43/0.63              = (k2_lattices @ sk_A @ sk_C_3 @ X0)))),
% 0.43/0.63      inference('clc', [status(thm)], ['22', '23'])).
% 0.43/0.63  thf('51', plain,
% 0.43/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_D_1)
% 0.43/0.63         = (k2_lattices @ sk_A @ sk_C_3 @ sk_D_1))),
% 0.43/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.63  thf('52', plain,
% 0.43/0.63      (((k2_lattices @ sk_A @ sk_C_3 @ (k3_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.43/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63            (k4_lattices @ sk_A @ sk_C_3 @ sk_D_1)))),
% 0.43/0.63      inference('demod', [status(thm)], ['29', '48', '51'])).
% 0.43/0.63  thf('53', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('54', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.63              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63                 (k2_lattices @ sk_A @ sk_C_3 @ X0))))),
% 0.43/0.63      inference('clc', [status(thm)], ['26', '27'])).
% 0.43/0.63  thf('55', plain,
% 0.43/0.63      (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.43/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63            (k2_lattices @ sk_A @ sk_C_3 @ sk_C_3)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.43/0.63  thf('56', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('57', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63              = (k1_lattices @ sk_A @ sk_B_3 @ X0)))),
% 0.43/0.63      inference('clc', [status(thm)], ['43', '44'])).
% 0.43/0.63  thf('58', plain,
% 0.43/0.63      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.43/0.63         = (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 0.43/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.43/0.63  thf('59', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('60', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d9_lattices, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.63       ( ( v9_lattices @ A ) <=>
% 0.43/0.63         ( ![B:$i]:
% 0.43/0.63           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.63             ( ![C:$i]:
% 0.43/0.63               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.63                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.43/0.63                   ( B ) ) ) ) ) ) ) ))).
% 0.43/0.63  thf('61', plain,
% 0.43/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.63         (~ (v9_lattices @ X13)
% 0.43/0.63          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.43/0.63          | ((k2_lattices @ X13 @ X15 @ (k1_lattices @ X13 @ X15 @ X14))
% 0.43/0.63              = (X15))
% 0.43/0.63          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.43/0.63          | ~ (l3_lattices @ X13)
% 0.43/0.63          | (v2_struct_0 @ X13))),
% 0.43/0.63      inference('cnf', [status(esa)], [d9_lattices])).
% 0.43/0.63  thf('62', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (l3_lattices @ sk_A)
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_3))
% 0.43/0.63              = (X0))
% 0.43/0.63          | ~ (v9_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.63  thf('63', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('64', plain,
% 0.43/0.63      (![X2 : $i]:
% 0.43/0.63         ((v2_struct_0 @ X2)
% 0.43/0.63          | ~ (v10_lattices @ X2)
% 0.43/0.63          | (v9_lattices @ X2)
% 0.43/0.63          | ~ (l3_lattices @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.43/0.63  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('66', plain,
% 0.43/0.63      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.43/0.63  thf('67', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('68', plain, ((v10_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('69', plain, ((v9_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.43/0.63  thf('70', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_3))
% 0.43/0.63              = (X0)))),
% 0.43/0.63      inference('demod', [status(thm)], ['62', '63', '69'])).
% 0.43/0.63  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('72', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_C_3))
% 0.43/0.63            = (X0))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('clc', [status(thm)], ['70', '71'])).
% 0.43/0.63  thf('73', plain,
% 0.43/0.63      (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_C_3 @ sk_C_3))
% 0.43/0.63         = (sk_C_3))),
% 0.43/0.63      inference('sup-', [status(thm)], ['59', '72'])).
% 0.43/0.63  thf('74', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(t17_lattices, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.43/0.63         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.63           ( ( k1_lattices @ A @ B @ B ) = ( B ) ) ) ) ))).
% 0.43/0.63  thf('75', plain,
% 0.43/0.63      (![X23 : $i, X24 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.43/0.63          | ((k1_lattices @ X24 @ X23 @ X23) = (X23))
% 0.43/0.63          | ~ (l3_lattices @ X24)
% 0.43/0.63          | ~ (v9_lattices @ X24)
% 0.43/0.63          | ~ (v8_lattices @ X24)
% 0.43/0.63          | ~ (v6_lattices @ X24)
% 0.43/0.63          | (v2_struct_0 @ X24))),
% 0.43/0.63      inference('cnf', [status(esa)], [t17_lattices])).
% 0.43/0.63  thf('76', plain,
% 0.43/0.63      (((v2_struct_0 @ sk_A)
% 0.43/0.63        | ~ (v6_lattices @ sk_A)
% 0.43/0.63        | ~ (v8_lattices @ sk_A)
% 0.43/0.63        | ~ (v9_lattices @ sk_A)
% 0.43/0.63        | ~ (l3_lattices @ sk_A)
% 0.43/0.63        | ((k1_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.43/0.63  thf('77', plain, ((v6_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.43/0.63  thf('78', plain,
% 0.43/0.63      (![X2 : $i]:
% 0.43/0.63         ((v2_struct_0 @ X2)
% 0.43/0.63          | ~ (v10_lattices @ X2)
% 0.43/0.63          | (v8_lattices @ X2)
% 0.43/0.63          | ~ (l3_lattices @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.43/0.63  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('80', plain,
% 0.43/0.63      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['78', '79'])).
% 0.43/0.63  thf('81', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('82', plain, ((v10_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('83', plain, ((v8_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.43/0.63  thf('84', plain, ((v9_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.43/0.63  thf('85', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('86', plain,
% 0.43/0.63      (((v2_struct_0 @ sk_A)
% 0.43/0.63        | ((k1_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3)))),
% 0.43/0.63      inference('demod', [status(thm)], ['76', '77', '83', '84', '85'])).
% 0.43/0.63  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('88', plain, (((k1_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3))),
% 0.43/0.63      inference('clc', [status(thm)], ['86', '87'])).
% 0.43/0.63  thf('89', plain, (((k2_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3))),
% 0.43/0.63      inference('demod', [status(thm)], ['73', '88'])).
% 0.43/0.63  thf('90', plain,
% 0.43/0.63      (((k2_lattices @ sk_A @ sk_C_3 @ (k3_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.43/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63            sk_C_3))),
% 0.43/0.63      inference('demod', [status(thm)], ['55', '58', '89'])).
% 0.43/0.63  thf('91', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('92', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d8_lattices, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.43/0.63       ( ( v8_lattices @ A ) <=>
% 0.43/0.63         ( ![B:$i]:
% 0.43/0.63           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.63             ( ![C:$i]:
% 0.43/0.63               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.63                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 0.43/0.63                   ( C ) ) ) ) ) ) ) ))).
% 0.43/0.63  thf('93', plain,
% 0.43/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.63         (~ (v8_lattices @ X10)
% 0.43/0.63          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.43/0.63          | ((k1_lattices @ X10 @ (k2_lattices @ X10 @ X12 @ X11) @ X11)
% 0.43/0.63              = (X11))
% 0.43/0.63          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.43/0.63          | ~ (l3_lattices @ X10)
% 0.43/0.63          | (v2_struct_0 @ X10))),
% 0.43/0.63      inference('cnf', [status(esa)], [d8_lattices])).
% 0.43/0.63  thf('94', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (l3_lattices @ sk_A)
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ sk_C_3)
% 0.43/0.63              = (sk_C_3))
% 0.43/0.63          | ~ (v8_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['92', '93'])).
% 0.43/0.63  thf('95', plain, ((l3_lattices @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('96', plain, ((v8_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.43/0.63  thf('97', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ sk_C_3)
% 0.43/0.63              = (sk_C_3)))),
% 0.43/0.63      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.43/0.63  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('99', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ sk_C_3)
% 0.43/0.63            = (sk_C_3))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('clc', [status(thm)], ['97', '98'])).
% 0.43/0.63  thf('100', plain,
% 0.43/0.63      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_C_3) @ sk_C_3)
% 0.43/0.63         = (sk_C_3))),
% 0.43/0.63      inference('sup-', [status(thm)], ['91', '99'])).
% 0.43/0.63  thf('101', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('102', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('103', plain,
% 0.43/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.43/0.63          | ~ (l1_lattices @ X21)
% 0.43/0.63          | ~ (v6_lattices @ X21)
% 0.43/0.63          | (v2_struct_0 @ X21)
% 0.43/0.63          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.43/0.63          | ((k4_lattices @ X21 @ X20 @ X22) = (k2_lattices @ X21 @ X20 @ X22)))),
% 0.43/0.63      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.43/0.63  thf('104', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63            = (k2_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (v6_lattices @ sk_A)
% 0.43/0.63          | ~ (l1_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['102', '103'])).
% 0.43/0.63  thf('105', plain, ((v6_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.43/0.63  thf('106', plain, ((l1_lattices @ sk_A)),
% 0.43/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.63  thf('107', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63            = (k2_lattices @ sk_A @ sk_B_3 @ X0))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.43/0.63  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('109', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 0.43/0.63      inference('clc', [status(thm)], ['107', '108'])).
% 0.43/0.63  thf('110', plain,
% 0.43/0.63      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.43/0.63         = (k2_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 0.43/0.63      inference('sup-', [status(thm)], ['101', '109'])).
% 0.43/0.63  thf('111', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('112', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(commutativity_k4_lattices, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.43/0.63         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.43/0.63         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.43/0.63  thf('113', plain,
% 0.43/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.43/0.63          | ~ (l1_lattices @ X4)
% 0.43/0.63          | ~ (v6_lattices @ X4)
% 0.43/0.63          | (v2_struct_0 @ X4)
% 0.43/0.63          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.43/0.63          | ((k4_lattices @ X4 @ X3 @ X5) = (k4_lattices @ X4 @ X5 @ X3)))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.43/0.63  thf('114', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63            = (k4_lattices @ sk_A @ X0 @ sk_B_3))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (v6_lattices @ sk_A)
% 0.43/0.63          | ~ (l1_lattices @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['112', '113'])).
% 0.43/0.63  thf('115', plain, ((v6_lattices @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.43/0.63  thf('116', plain, ((l1_lattices @ sk_A)),
% 0.43/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.63  thf('117', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63            = (k4_lattices @ sk_A @ X0 @ sk_B_3))
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | (v2_struct_0 @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.43/0.63  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('119', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.43/0.63              = (k4_lattices @ sk_A @ X0 @ sk_B_3)))),
% 0.43/0.63      inference('clc', [status(thm)], ['117', '118'])).
% 0.43/0.63  thf('120', plain,
% 0.43/0.63      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.43/0.63         = (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 0.43/0.63      inference('sup-', [status(thm)], ['111', '119'])).
% 0.43/0.63  thf('121', plain,
% 0.43/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 0.43/0.63         = (k2_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 0.43/0.63      inference('demod', [status(thm)], ['110', '120'])).
% 0.43/0.63  thf('122', plain,
% 0.43/0.63      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ sk_C_3)
% 0.43/0.63         = (sk_C_3))),
% 0.43/0.63      inference('demod', [status(thm)], ['100', '121'])).
% 0.43/0.63  thf('123', plain,
% 0.43/0.63      (((k2_lattices @ sk_A @ sk_C_3 @ (k3_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.43/0.63         = (sk_C_3))),
% 0.43/0.63      inference('sup+', [status(thm)], ['90', '122'])).
% 0.43/0.63  thf('124', plain,
% 0.43/0.63      (((sk_C_3)
% 0.43/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.43/0.63            (k4_lattices @ sk_A @ sk_C_3 @ sk_D_1)))),
% 0.43/0.63      inference('demod', [status(thm)], ['52', '123'])).
% 0.43/0.63  thf('125', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('126', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('127', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         ((v2_struct_0 @ sk_A)
% 0.43/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.43/0.63          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_3 @ X1))
% 0.43/0.63              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ 
% 0.45/0.63                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 0.45/0.63      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.63  thf('128', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.45/0.63            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_D_1 @ sk_B_3) @ 
% 0.45/0.63               (k2_lattices @ sk_A @ sk_D_1 @ X0)))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['126', '127'])).
% 0.45/0.63  thf('129', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('130', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('131', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.45/0.63          | ~ (l1_lattices @ X21)
% 0.45/0.63          | ~ (v6_lattices @ X21)
% 0.45/0.63          | (v2_struct_0 @ X21)
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.45/0.63          | ((k4_lattices @ X21 @ X20 @ X22) = (k2_lattices @ X21 @ X20 @ X22)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.45/0.63  thf('132', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.45/0.63            = (k2_lattices @ sk_A @ sk_D_1 @ X0))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (v6_lattices @ sk_A)
% 0.45/0.63          | ~ (l1_lattices @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['130', '131'])).
% 0.45/0.63  thf('133', plain, ((v6_lattices @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.45/0.63  thf('134', plain, ((l1_lattices @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.63  thf('135', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.45/0.63            = (k2_lattices @ sk_A @ sk_D_1 @ X0))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.45/0.63  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('137', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.45/0.63              = (k2_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.45/0.63      inference('clc', [status(thm)], ['135', '136'])).
% 0.45/0.63  thf('138', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_D_1 @ sk_B_3)
% 0.45/0.63         = (k2_lattices @ sk_A @ sk_D_1 @ sk_B_3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['129', '137'])).
% 0.45/0.63  thf('139', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.45/0.63         = (k4_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('140', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.45/0.63         = (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['111', '119'])).
% 0.45/0.63  thf('141', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 0.45/0.63         = (k4_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['139', '140'])).
% 0.45/0.63  thf('142', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('143', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.45/0.63              = (k4_lattices @ sk_A @ X0 @ sk_B_3)))),
% 0.45/0.63      inference('clc', [status(thm)], ['117', '118'])).
% 0.45/0.63  thf('144', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_B_3 @ sk_D_1)
% 0.45/0.63         = (k4_lattices @ sk_A @ sk_D_1 @ sk_B_3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['142', '143'])).
% 0.45/0.63  thf('145', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 0.45/0.63         = (k4_lattices @ sk_A @ sk_D_1 @ sk_B_3))),
% 0.45/0.63      inference('sup+', [status(thm)], ['141', '144'])).
% 0.45/0.63  thf('146', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 0.45/0.63         = (k2_lattices @ sk_A @ sk_D_1 @ sk_B_3))),
% 0.45/0.63      inference('demod', [status(thm)], ['138', '145'])).
% 0.45/0.63  thf('147', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.45/0.63            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63               (k2_lattices @ sk_A @ sk_D_1 @ X0)))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['128', '146'])).
% 0.45/0.63  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('149', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.45/0.63              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63                 (k2_lattices @ sk_A @ sk_D_1 @ X0))))),
% 0.45/0.63      inference('clc', [status(thm)], ['147', '148'])).
% 0.45/0.63  thf('150', plain,
% 0.45/0.63      (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.45/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63            (k2_lattices @ sk_A @ sk_D_1 @ sk_C_3)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['125', '149'])).
% 0.45/0.63  thf('151', plain,
% 0.45/0.63      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.45/0.63         = (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.63  thf('152', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('153', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.45/0.63              = (k2_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.45/0.63      inference('clc', [status(thm)], ['135', '136'])).
% 0.45/0.63  thf('154', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_D_1 @ sk_C_3)
% 0.45/0.63         = (k2_lattices @ sk_A @ sk_D_1 @ sk_C_3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['152', '153'])).
% 0.45/0.63  thf('155', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('156', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('157', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.45/0.63          | ~ (l1_lattices @ X4)
% 0.45/0.63          | ~ (v6_lattices @ X4)
% 0.45/0.63          | (v2_struct_0 @ X4)
% 0.45/0.63          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.45/0.63          | ((k4_lattices @ X4 @ X3 @ X5) = (k4_lattices @ X4 @ X5 @ X3)))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.45/0.63  thf('158', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 0.45/0.63            = (k4_lattices @ sk_A @ X0 @ sk_C_3))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (v6_lattices @ sk_A)
% 0.45/0.63          | ~ (l1_lattices @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['156', '157'])).
% 0.45/0.63  thf('159', plain, ((v6_lattices @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.45/0.63  thf('160', plain, ((l1_lattices @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.63  thf('161', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 0.45/0.63            = (k4_lattices @ sk_A @ X0 @ sk_C_3))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.45/0.63  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('163', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 0.45/0.63              = (k4_lattices @ sk_A @ X0 @ sk_C_3)))),
% 0.45/0.63      inference('clc', [status(thm)], ['161', '162'])).
% 0.45/0.63  thf('164', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_D_1)
% 0.45/0.63         = (k4_lattices @ sk_A @ sk_D_1 @ sk_C_3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['155', '163'])).
% 0.45/0.63  thf('165', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_D_1)
% 0.45/0.63         = (k2_lattices @ sk_A @ sk_D_1 @ sk_C_3))),
% 0.45/0.63      inference('demod', [status(thm)], ['154', '164'])).
% 0.45/0.63  thf('166', plain,
% 0.45/0.63      (((k2_lattices @ sk_A @ sk_D_1 @ (k3_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.45/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63            (k4_lattices @ sk_A @ sk_C_3 @ sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['150', '151', '165'])).
% 0.45/0.63  thf('167', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('168', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 0.45/0.63              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63                 (k2_lattices @ sk_A @ sk_D_1 @ X0))))),
% 0.45/0.63      inference('clc', [status(thm)], ['147', '148'])).
% 0.45/0.63  thf('169', plain,
% 0.45/0.63      (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_3 @ sk_D_1))
% 0.45/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63            (k2_lattices @ sk_A @ sk_D_1 @ sk_D_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['167', '168'])).
% 0.45/0.63  thf('170', plain,
% 0.45/0.63      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 0.45/0.63         = (k1_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['46', '47'])).
% 0.45/0.63  thf('171', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('172', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('173', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.63         (~ (v9_lattices @ X13)
% 0.45/0.63          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.45/0.63          | ((k2_lattices @ X13 @ X15 @ (k1_lattices @ X13 @ X15 @ X14))
% 0.45/0.63              = (X15))
% 0.45/0.63          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.45/0.63          | ~ (l3_lattices @ X13)
% 0.45/0.63          | (v2_struct_0 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [d9_lattices])).
% 0.45/0.63  thf('174', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (l3_lattices @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_D_1))
% 0.45/0.63              = (X0))
% 0.45/0.63          | ~ (v9_lattices @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['172', '173'])).
% 0.45/0.63  thf('175', plain, ((l3_lattices @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('176', plain, ((v9_lattices @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.45/0.63  thf('177', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_D_1))
% 0.45/0.63              = (X0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['174', '175', '176'])).
% 0.45/0.63  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('179', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_D_1))
% 0.45/0.63            = (X0))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('clc', [status(thm)], ['177', '178'])).
% 0.45/0.63  thf('180', plain,
% 0.45/0.63      (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_D_1 @ sk_D_1))
% 0.45/0.63         = (sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['171', '179'])).
% 0.45/0.63  thf('181', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('182', plain,
% 0.45/0.63      (![X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.45/0.63          | ((k1_lattices @ X24 @ X23 @ X23) = (X23))
% 0.45/0.63          | ~ (l3_lattices @ X24)
% 0.45/0.63          | ~ (v9_lattices @ X24)
% 0.45/0.63          | ~ (v8_lattices @ X24)
% 0.45/0.63          | ~ (v6_lattices @ X24)
% 0.45/0.63          | (v2_struct_0 @ X24))),
% 0.45/0.63      inference('cnf', [status(esa)], [t17_lattices])).
% 0.45/0.63  thf('183', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (v6_lattices @ sk_A)
% 0.45/0.63        | ~ (v8_lattices @ sk_A)
% 0.45/0.63        | ~ (v9_lattices @ sk_A)
% 0.45/0.63        | ~ (l3_lattices @ sk_A)
% 0.45/0.63        | ((k1_lattices @ sk_A @ sk_D_1 @ sk_D_1) = (sk_D_1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['181', '182'])).
% 0.45/0.63  thf('184', plain, ((v6_lattices @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.45/0.63  thf('185', plain, ((v8_lattices @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.45/0.63  thf('186', plain, ((v9_lattices @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.45/0.63  thf('187', plain, ((l3_lattices @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('188', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A)
% 0.45/0.63        | ((k1_lattices @ sk_A @ sk_D_1 @ sk_D_1) = (sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['183', '184', '185', '186', '187'])).
% 0.45/0.63  thf('189', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('190', plain, (((k1_lattices @ sk_A @ sk_D_1 @ sk_D_1) = (sk_D_1))),
% 0.45/0.63      inference('clc', [status(thm)], ['188', '189'])).
% 0.45/0.63  thf('191', plain, (((k2_lattices @ sk_A @ sk_D_1 @ sk_D_1) = (sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['180', '190'])).
% 0.45/0.63  thf('192', plain,
% 0.45/0.63      (((k2_lattices @ sk_A @ sk_D_1 @ (k3_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.45/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63            sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['169', '170', '191'])).
% 0.45/0.63  thf('193', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('194', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('195', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         (~ (v8_lattices @ X10)
% 0.45/0.63          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.45/0.63          | ((k1_lattices @ X10 @ (k2_lattices @ X10 @ X12 @ X11) @ X11)
% 0.45/0.63              = (X11))
% 0.45/0.63          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.45/0.63          | ~ (l3_lattices @ X10)
% 0.45/0.63          | (v2_struct_0 @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [d8_lattices])).
% 0.45/0.63  thf('196', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (l3_lattices @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_1) @ sk_D_1)
% 0.45/0.63              = (sk_D_1))
% 0.45/0.63          | ~ (v8_lattices @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['194', '195'])).
% 0.45/0.63  thf('197', plain, ((l3_lattices @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('198', plain, ((v8_lattices @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.45/0.63  thf('199', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_1) @ sk_D_1)
% 0.45/0.63              = (sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.45/0.63  thf('200', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('201', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_1) @ sk_D_1)
% 0.45/0.63            = (sk_D_1))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('clc', [status(thm)], ['199', '200'])).
% 0.45/0.63  thf('202', plain,
% 0.45/0.63      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1) @ sk_D_1)
% 0.45/0.63         = (sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['193', '201'])).
% 0.45/0.63  thf('203', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('204', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.63          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 0.45/0.63              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 0.45/0.63      inference('clc', [status(thm)], ['107', '108'])).
% 0.45/0.63  thf('205', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_B_3 @ sk_D_1)
% 0.45/0.63         = (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['203', '204'])).
% 0.45/0.63  thf('206', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 0.45/0.63         = (k4_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['139', '140'])).
% 0.45/0.63  thf('207', plain,
% 0.45/0.63      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 0.45/0.63         = (k2_lattices @ sk_A @ sk_B_3 @ sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['205', '206'])).
% 0.45/0.63  thf('208', plain,
% 0.45/0.63      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ sk_D_1)
% 0.45/0.63         = (sk_D_1))),
% 0.45/0.63      inference('demod', [status(thm)], ['202', '207'])).
% 0.45/0.63  thf('209', plain,
% 0.45/0.63      (((k2_lattices @ sk_A @ sk_D_1 @ (k3_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 0.45/0.63         = (sk_D_1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['192', '208'])).
% 0.45/0.63  thf('210', plain,
% 0.45/0.63      (((sk_D_1)
% 0.45/0.63         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 0.45/0.63            (k4_lattices @ sk_A @ sk_C_3 @ sk_D_1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['166', '209'])).
% 0.45/0.63  thf('211', plain, (((sk_D_1) = (sk_C_3))),
% 0.45/0.63      inference('sup+', [status(thm)], ['124', '210'])).
% 0.45/0.63  thf('212', plain, (((sk_C_3) != (sk_D_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('213', plain, ($false),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['211', '212'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
