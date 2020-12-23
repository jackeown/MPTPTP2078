%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iTowjgGEZg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:32 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 674 expanded)
%              Number of leaves         :   31 ( 208 expanded)
%              Depth                    :   16
%              Number of atoms          : 1818 (14544 expanded)
%              Number of equality atoms :  100 ( 947 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v11_lattices @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k2_lattices @ X7 @ X9 @ ( k1_lattices @ X7 @ X8 @ X10 ) )
        = ( k1_lattices @ X7 @ ( k2_lattices @ X7 @ X9 @ X8 ) @ ( k2_lattices @ X7 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_lattices @ X19 )
      | ~ ( v6_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( ( k4_lattices @ X19 @ X18 @ X20 )
        = ( k2_lattices @ X19 @ X18 @ X20 ) ) ) ),
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
    ! [X14: $i] :
      ( ( l1_lattices @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l2_lattices @ X16 )
      | ~ ( v4_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k3_lattices @ X16 @ X15 @ X17 )
        = ( k1_lattices @ X16 @ X15 @ X17 ) ) ) ),
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
    ! [X14: $i] :
      ( ( l2_lattices @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
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

thf('48',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k3_lattices @ A @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('53',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k3_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['47','57'])).

thf('59',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v9_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k1_lattices @ X11 @ X13 @ X12 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['63','64','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k1_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['60','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l2_lattices @ X16 )
      | ~ ( v4_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k3_lattices @ X16 @ X15 @ X17 )
        = ( k1_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('80',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k1_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( k2_lattices @ sk_A @ sk_C_2 @ ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['74','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('88',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_C_2
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','59','85','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_2 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_lattices @ X19 )
      | ~ ( v6_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( ( k4_lattices @ X19 @ X18 @ X20 )
        = ( k2_lattices @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) )
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
      ( ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
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

thf('107',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( ( k4_lattices @ X5 @ X4 @ X6 )
        = ( k4_lattices @ X5 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('110',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['104','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('118',plain,
    ( ( k4_lattices @ sk_A @ sk_B_2 @ sk_D_1 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['103','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['90','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('127',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('129',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('132',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k1_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l2_lattices @ X16 )
      | ~ ( v4_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k3_lattices @ X16 @ X15 @ X17 )
        = ( k1_lattices @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('138',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k3_lattices @ sk_A @ sk_D_1 @ sk_B_2 )
    = ( k1_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['133','141'])).

thf('143',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k3_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['47','57'])).

thf('144',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('146',plain,
    ( ( k3_lattices @ sk_A @ sk_B_2 @ sk_D_1 )
    = ( k3_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k3_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['143','146'])).

thf('148',plain,
    ( ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 )
    = ( k1_lattices @ sk_A @ sk_D_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['142','147'])).

thf('149',plain,
    ( ( k2_lattices @ sk_A @ sk_D_1 @ ( k3_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) )
    = sk_D_1 ),
    inference(demod,[status(thm)],['132','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('152',plain,
    ( ( k4_lattices @ sk_A @ sk_D_1 @ sk_C_2 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( ( k4_lattices @ X5 @ X4 @ X6 )
        = ( k4_lattices @ X5 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('158',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_2 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
    = ( k4_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['153','161'])).

thf('163',plain,
    ( ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
    = ( k2_lattices @ sk_A @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['152','162'])).

thf('164',plain,
    ( sk_D_1
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_B_2 ) @ ( k4_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['124','129','149','163'])).

thf('165',plain,(
    sk_D_1 = sk_C_2 ),
    inference('sup+',[status(thm)],['89','164'])).

thf('166',plain,(
    sk_C_2 != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iTowjgGEZg
% 0.14/0.38  % Computer   : n008.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 09:52:15 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.39  % Number of cores: 8
% 0.14/0.39  % Python version: Python 3.6.8
% 0.24/0.39  % Running in FO mode
% 0.35/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.60  % Solved by: fo/fo7.sh
% 0.35/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.60  % done 154 iterations in 0.100s
% 0.35/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.60  % SZS output start Refutation
% 0.35/0.60  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.35/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.60  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.35/0.60  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.35/0.60  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.35/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.35/0.60  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.35/0.60  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.35/0.60  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.35/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.60  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 0.35/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.35/0.60  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.35/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.60  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.35/0.60  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.35/0.60  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.35/0.60  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.35/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.60  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.35/0.60  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.35/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.60  thf(t32_lattices, conjecture,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.35/0.60         ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60           ( ![C:$i]:
% 0.35/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60               ( ![D:$i]:
% 0.35/0.60                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60                   ( ( ( ( k4_lattices @ A @ B @ C ) =
% 0.35/0.60                         ( k4_lattices @ A @ B @ D ) ) & 
% 0.35/0.60                       ( ( k3_lattices @ A @ B @ C ) =
% 0.35/0.60                         ( k3_lattices @ A @ B @ D ) ) ) =>
% 0.35/0.60                     ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.60    (~( ![A:$i]:
% 0.35/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.35/0.60            ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.35/0.60          ( ![B:$i]:
% 0.35/0.60            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60              ( ![C:$i]:
% 0.35/0.60                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60                  ( ![D:$i]:
% 0.35/0.60                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60                      ( ( ( ( k4_lattices @ A @ B @ C ) =
% 0.35/0.60                            ( k4_lattices @ A @ B @ D ) ) & 
% 0.35/0.60                          ( ( k3_lattices @ A @ B @ C ) =
% 0.35/0.60                            ( k3_lattices @ A @ B @ D ) ) ) =>
% 0.35/0.60                        ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.60    inference('cnf.neg', [status(esa)], [t32_lattices])).
% 0.35/0.60  thf('0', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(d11_lattices, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.35/0.60       ( ( v11_lattices @ A ) <=>
% 0.35/0.60         ( ![B:$i]:
% 0.35/0.60           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60             ( ![C:$i]:
% 0.35/0.60               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60                 ( ![D:$i]:
% 0.35/0.60                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60                     ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) ) =
% 0.35/0.60                       ( k1_lattices @
% 0.35/0.60                         A @ ( k2_lattices @ A @ B @ C ) @ 
% 0.35/0.60                         ( k2_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.60  thf('3', plain,
% 0.35/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.60         (~ (v11_lattices @ X7)
% 0.35/0.60          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.35/0.60          | ((k2_lattices @ X7 @ X9 @ (k1_lattices @ X7 @ X8 @ X10))
% 0.35/0.60              = (k1_lattices @ X7 @ (k2_lattices @ X7 @ X9 @ X8) @ 
% 0.35/0.60                 (k2_lattices @ X7 @ X9 @ X10)))
% 0.35/0.60          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 0.35/0.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.35/0.60          | ~ (l3_lattices @ X7)
% 0.35/0.60          | (v2_struct_0 @ X7))),
% 0.35/0.60      inference('cnf', [status(esa)], [d11_lattices])).
% 0.35/0.60  thf('4', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         ((v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (l3_lattices @ sk_A)
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ X1))
% 0.35/0.60              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ 
% 0.35/0.60                 (k2_lattices @ sk_A @ X0 @ X1)))
% 0.35/0.60          | ~ (v11_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.60  thf('5', plain, ((l3_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('6', plain, ((v11_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('7', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         ((v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ X1))
% 0.35/0.60              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ 
% 0.35/0.60                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 0.35/0.60      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.35/0.60  thf('8', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60               (k2_lattices @ sk_A @ sk_C_2 @ X0)))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['1', '7'])).
% 0.35/0.60  thf('9', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('10', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(redefinition_k4_lattices, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.35/0.60         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.35/0.60  thf('11', plain,
% 0.35/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.35/0.60          | ~ (l1_lattices @ X19)
% 0.35/0.60          | ~ (v6_lattices @ X19)
% 0.35/0.60          | (v2_struct_0 @ X19)
% 0.35/0.60          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.35/0.60          | ((k4_lattices @ X19 @ X18 @ X20) = (k2_lattices @ X19 @ X18 @ X20)))),
% 0.35/0.60      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.35/0.60  thf('12', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60            = (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v6_lattices @ sk_A)
% 0.35/0.60          | ~ (l1_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.60  thf(cc1_lattices, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l3_lattices @ A ) =>
% 0.35/0.60       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.35/0.60         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.35/0.60           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.35/0.60           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.35/0.60  thf('13', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         ((v2_struct_0 @ X0)
% 0.35/0.60          | ~ (v10_lattices @ X0)
% 0.35/0.60          | (v6_lattices @ X0)
% 0.35/0.60          | ~ (l3_lattices @ X0))),
% 0.35/0.60      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.35/0.60  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('15', plain,
% 0.35/0.60      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.60  thf('16', plain, ((l3_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('17', plain, ((v10_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('18', plain, ((v6_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.35/0.60  thf('19', plain, ((l3_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(dt_l3_lattices, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.35/0.60  thf('20', plain,
% 0.35/0.60      (![X14 : $i]: ((l1_lattices @ X14) | ~ (l3_lattices @ X14))),
% 0.35/0.60      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.35/0.60  thf('21', plain, ((l1_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.60  thf('22', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60            = (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['12', '18', '21'])).
% 0.35/0.60  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('24', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60              = (k2_lattices @ sk_A @ sk_C_2 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['22', '23'])).
% 0.35/0.60  thf('25', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k2_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['9', '24'])).
% 0.35/0.60  thf('26', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60               (k2_lattices @ sk_A @ sk_C_2 @ X0)))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['8', '25'])).
% 0.35/0.60  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('28', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60                 (k2_lattices @ sk_A @ sk_C_2 @ X0))))),
% 0.35/0.60      inference('clc', [status(thm)], ['26', '27'])).
% 0.35/0.60  thf('29', plain,
% 0.35/0.60      (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))
% 0.35/0.60         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60            (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['0', '28'])).
% 0.35/0.60  thf('30', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('31', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(redefinition_k3_lattices, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.35/0.60         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.35/0.60  thf('32', plain,
% 0.35/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.35/0.60          | ~ (l2_lattices @ X16)
% 0.35/0.60          | ~ (v4_lattices @ X16)
% 0.35/0.60          | (v2_struct_0 @ X16)
% 0.35/0.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.35/0.60          | ((k3_lattices @ X16 @ X15 @ X17) = (k1_lattices @ X16 @ X15 @ X17)))),
% 0.35/0.60      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.35/0.60  thf('33', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60            = (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v4_lattices @ sk_A)
% 0.35/0.60          | ~ (l2_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.60  thf('34', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         ((v2_struct_0 @ X0)
% 0.35/0.60          | ~ (v10_lattices @ X0)
% 0.35/0.60          | (v4_lattices @ X0)
% 0.35/0.60          | ~ (l3_lattices @ X0))),
% 0.35/0.60      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.35/0.60  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('36', plain,
% 0.35/0.60      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.60  thf('37', plain, ((l3_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('38', plain, ((v10_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('39', plain, ((v4_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.35/0.60  thf('40', plain, ((l3_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('41', plain,
% 0.35/0.60      (![X14 : $i]: ((l2_lattices @ X14) | ~ (l3_lattices @ X14))),
% 0.35/0.60      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.35/0.60  thf('42', plain, ((l2_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.60  thf('43', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60            = (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['33', '39', '42'])).
% 0.35/0.60  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('45', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60              = (k1_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['43', '44'])).
% 0.35/0.60  thf('46', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_B_2 @ sk_D_1)
% 0.35/0.60         = (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.35/0.60      inference('sup-', [status(thm)], ['30', '45'])).
% 0.35/0.60  thf('47', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.35/0.60         = (k3_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('48', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('49', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(commutativity_k3_lattices, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.35/0.60         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 0.35/0.60  thf('50', plain,
% 0.35/0.60      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.35/0.60          | ~ (l2_lattices @ X2)
% 0.35/0.60          | ~ (v4_lattices @ X2)
% 0.35/0.60          | (v2_struct_0 @ X2)
% 0.35/0.60          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.35/0.60          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 0.35/0.60      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 0.35/0.60  thf('51', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60            = (k3_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v4_lattices @ sk_A)
% 0.35/0.60          | ~ (l2_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.60  thf('52', plain, ((v4_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.35/0.60  thf('53', plain, ((l2_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.60  thf('54', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60            = (k3_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.35/0.60  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('56', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60              = (k3_lattices @ sk_A @ X0 @ sk_B_2)))),
% 0.35/0.60      inference('clc', [status(thm)], ['54', '55'])).
% 0.35/0.60  thf('57', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.35/0.60         = (k3_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['48', '56'])).
% 0.35/0.60  thf('58', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k3_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.35/0.60      inference('demod', [status(thm)], ['47', '57'])).
% 0.35/0.60  thf('59', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k1_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.35/0.60      inference('demod', [status(thm)], ['46', '58'])).
% 0.35/0.60  thf('60', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('61', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(d9_lattices, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.35/0.60       ( ( v9_lattices @ A ) <=>
% 0.35/0.60         ( ![B:$i]:
% 0.35/0.60           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60             ( ![C:$i]:
% 0.35/0.60               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.60                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.35/0.60                   ( B ) ) ) ) ) ) ) ))).
% 0.35/0.60  thf('62', plain,
% 0.35/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.60         (~ (v9_lattices @ X11)
% 0.35/0.60          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.35/0.60          | ((k2_lattices @ X11 @ X13 @ (k1_lattices @ X11 @ X13 @ X12))
% 0.35/0.60              = (X13))
% 0.35/0.60          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.35/0.60          | ~ (l3_lattices @ X11)
% 0.35/0.60          | (v2_struct_0 @ X11))),
% 0.35/0.60      inference('cnf', [status(esa)], [d9_lattices])).
% 0.35/0.60  thf('63', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         ((v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (l3_lattices @ sk_A)
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60              = (X0))
% 0.35/0.60          | ~ (v9_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.35/0.60  thf('64', plain, ((l3_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('65', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         ((v2_struct_0 @ X0)
% 0.35/0.60          | ~ (v10_lattices @ X0)
% 0.35/0.60          | (v9_lattices @ X0)
% 0.35/0.60          | ~ (l3_lattices @ X0))),
% 0.35/0.60      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.35/0.60  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('67', plain,
% 0.35/0.60      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.60  thf('68', plain, ((l3_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('69', plain, ((v10_lattices @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('70', plain, ((v9_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.35/0.60  thf('71', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         ((v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60              = (X0)))),
% 0.35/0.60      inference('demod', [status(thm)], ['63', '64', '70'])).
% 0.35/0.60  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('73', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60            = (X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('clc', [status(thm)], ['71', '72'])).
% 0.35/0.60  thf('74', plain,
% 0.35/0.60      (((k2_lattices @ sk_A @ sk_C_2 @ (k1_lattices @ sk_A @ sk_C_2 @ sk_B_2))
% 0.35/0.60         = (sk_C_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['60', '73'])).
% 0.35/0.60  thf('75', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('76', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('77', plain,
% 0.35/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.35/0.60          | ~ (l2_lattices @ X16)
% 0.35/0.60          | ~ (v4_lattices @ X16)
% 0.35/0.60          | (v2_struct_0 @ X16)
% 0.35/0.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.35/0.60          | ((k3_lattices @ X16 @ X15 @ X17) = (k1_lattices @ X16 @ X15 @ X17)))),
% 0.35/0.60      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.35/0.60  thf('78', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60            = (k1_lattices @ sk_A @ sk_C_2 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v4_lattices @ sk_A)
% 0.35/0.60          | ~ (l2_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['76', '77'])).
% 0.35/0.60  thf('79', plain, ((v4_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.35/0.60  thf('80', plain, ((l2_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.60  thf('81', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60            = (k1_lattices @ sk_A @ sk_C_2 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.35/0.60  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('83', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k3_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60              = (k1_lattices @ sk_A @ sk_C_2 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['81', '82'])).
% 0.35/0.60  thf('84', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k1_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['75', '83'])).
% 0.35/0.60  thf('85', plain,
% 0.35/0.60      (((k2_lattices @ sk_A @ sk_C_2 @ (k3_lattices @ sk_A @ sk_C_2 @ sk_B_2))
% 0.35/0.60         = (sk_C_2))),
% 0.35/0.60      inference('demod', [status(thm)], ['74', '84'])).
% 0.35/0.60  thf('86', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('87', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60              = (k2_lattices @ sk_A @ sk_C_2 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['22', '23'])).
% 0.35/0.60  thf('88', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 0.35/0.60         = (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))),
% 0.35/0.60      inference('sup-', [status(thm)], ['86', '87'])).
% 0.35/0.60  thf('89', plain,
% 0.35/0.60      (((sk_C_2)
% 0.35/0.60         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60            (k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.35/0.60      inference('demod', [status(thm)], ['29', '59', '85', '88'])).
% 0.35/0.60  thf('90', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('91', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('92', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         ((v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_2 @ X1))
% 0.35/0.60              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_2) @ 
% 0.35/0.60                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 0.35/0.60      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.35/0.60  thf('93', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_D_1 @ sk_B_2) @ 
% 0.35/0.60               (k2_lattices @ sk_A @ sk_D_1 @ X0)))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['91', '92'])).
% 0.35/0.60  thf('94', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('95', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('96', plain,
% 0.35/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.35/0.60          | ~ (l1_lattices @ X19)
% 0.35/0.60          | ~ (v6_lattices @ X19)
% 0.35/0.60          | (v2_struct_0 @ X19)
% 0.35/0.60          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.35/0.60          | ((k4_lattices @ X19 @ X18 @ X20) = (k2_lattices @ X19 @ X18 @ X20)))),
% 0.35/0.60      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.35/0.60  thf('97', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.35/0.60            = (k2_lattices @ sk_A @ sk_D_1 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v6_lattices @ sk_A)
% 0.35/0.60          | ~ (l1_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['95', '96'])).
% 0.35/0.60  thf('98', plain, ((v6_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.35/0.60  thf('99', plain, ((l1_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.60  thf('100', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.35/0.60            = (k2_lattices @ sk_A @ sk_D_1 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.35/0.60  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('102', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.35/0.60              = (k2_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['100', '101'])).
% 0.35/0.60  thf('103', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_D_1 @ sk_B_2)
% 0.35/0.60         = (k2_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['94', '102'])).
% 0.35/0.60  thf('104', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.35/0.60         = (k4_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('105', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('106', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(commutativity_k4_lattices, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.35/0.60         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.60       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 0.35/0.60  thf('107', plain,
% 0.35/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.35/0.60          | ~ (l1_lattices @ X5)
% 0.35/0.60          | ~ (v6_lattices @ X5)
% 0.35/0.60          | (v2_struct_0 @ X5)
% 0.35/0.60          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.35/0.60          | ((k4_lattices @ X5 @ X4 @ X6) = (k4_lattices @ X5 @ X6 @ X4)))),
% 0.35/0.60      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.35/0.60  thf('108', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v6_lattices @ sk_A)
% 0.35/0.60          | ~ (l1_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['106', '107'])).
% 0.35/0.60  thf('109', plain, ((v6_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.35/0.60  thf('110', plain, ((l1_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.60  thf('111', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60            = (k4_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.35/0.60  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('113', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60              = (k4_lattices @ sk_A @ X0 @ sk_B_2)))),
% 0.35/0.60      inference('clc', [status(thm)], ['111', '112'])).
% 0.35/0.60  thf('114', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.35/0.60         = (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['105', '113'])).
% 0.35/0.60  thf('115', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k4_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.35/0.60      inference('demod', [status(thm)], ['104', '114'])).
% 0.35/0.60  thf('116', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('117', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k4_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60              = (k4_lattices @ sk_A @ X0 @ sk_B_2)))),
% 0.35/0.60      inference('clc', [status(thm)], ['111', '112'])).
% 0.35/0.60  thf('118', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_B_2 @ sk_D_1)
% 0.35/0.60         = (k4_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['116', '117'])).
% 0.35/0.60  thf('119', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k4_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('sup+', [status(thm)], ['115', '118'])).
% 0.35/0.60  thf('120', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k2_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('demod', [status(thm)], ['103', '119'])).
% 0.35/0.60  thf('121', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60               (k2_lattices @ sk_A @ sk_D_1 @ X0)))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['93', '120'])).
% 0.35/0.60  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('123', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ X0))
% 0.35/0.60              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60                 (k2_lattices @ sk_A @ sk_D_1 @ X0))))),
% 0.35/0.60      inference('clc', [status(thm)], ['121', '122'])).
% 0.35/0.60  thf('124', plain,
% 0.35/0.60      (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))
% 0.35/0.60         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60            (k2_lattices @ sk_A @ sk_D_1 @ sk_C_2)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['90', '123'])).
% 0.35/0.60  thf('125', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('126', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60              = (k1_lattices @ sk_A @ sk_B_2 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['43', '44'])).
% 0.35/0.60  thf('127', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.35/0.60         = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['125', '126'])).
% 0.35/0.60  thf('128', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 0.35/0.60         = (k3_lattices @ sk_A @ sk_C_2 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['48', '56'])).
% 0.35/0.60  thf('129', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k1_lattices @ sk_A @ sk_B_2 @ sk_C_2))),
% 0.35/0.60      inference('demod', [status(thm)], ['127', '128'])).
% 0.35/0.60  thf('130', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('131', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.35/0.60            = (X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('clc', [status(thm)], ['71', '72'])).
% 0.35/0.60  thf('132', plain,
% 0.35/0.60      (((k2_lattices @ sk_A @ sk_D_1 @ (k1_lattices @ sk_A @ sk_D_1 @ sk_B_2))
% 0.35/0.60         = (sk_D_1))),
% 0.35/0.60      inference('sup-', [status(thm)], ['130', '131'])).
% 0.35/0.60  thf('133', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('134', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('135', plain,
% 0.35/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.35/0.60          | ~ (l2_lattices @ X16)
% 0.35/0.60          | ~ (v4_lattices @ X16)
% 0.35/0.60          | (v2_struct_0 @ X16)
% 0.35/0.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.35/0.60          | ((k3_lattices @ X16 @ X15 @ X17) = (k1_lattices @ X16 @ X15 @ X17)))),
% 0.35/0.60      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.35/0.60  thf('136', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_D_1 @ X0)
% 0.35/0.60            = (k1_lattices @ sk_A @ sk_D_1 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v4_lattices @ sk_A)
% 0.35/0.60          | ~ (l2_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['134', '135'])).
% 0.35/0.60  thf('137', plain, ((v4_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.35/0.60  thf('138', plain, ((l2_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.60  thf('139', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k3_lattices @ sk_A @ sk_D_1 @ X0)
% 0.35/0.60            = (k1_lattices @ sk_A @ sk_D_1 @ X0))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.35/0.60  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('141', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k3_lattices @ sk_A @ sk_D_1 @ X0)
% 0.35/0.60              = (k1_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['139', '140'])).
% 0.35/0.60  thf('142', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_D_1 @ sk_B_2)
% 0.35/0.60         = (k1_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['133', '141'])).
% 0.35/0.60  thf('143', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k3_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 0.35/0.60      inference('demod', [status(thm)], ['47', '57'])).
% 0.35/0.60  thf('144', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('145', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k3_lattices @ sk_A @ sk_B_2 @ X0)
% 0.35/0.60              = (k3_lattices @ sk_A @ X0 @ sk_B_2)))),
% 0.35/0.60      inference('clc', [status(thm)], ['54', '55'])).
% 0.35/0.60  thf('146', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_B_2 @ sk_D_1)
% 0.35/0.60         = (k3_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['144', '145'])).
% 0.35/0.60  thf('147', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k3_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('sup+', [status(thm)], ['143', '146'])).
% 0.35/0.60  thf('148', plain,
% 0.35/0.60      (((k3_lattices @ sk_A @ sk_C_2 @ sk_B_2)
% 0.35/0.60         = (k1_lattices @ sk_A @ sk_D_1 @ sk_B_2))),
% 0.35/0.60      inference('demod', [status(thm)], ['142', '147'])).
% 0.35/0.60  thf('149', plain,
% 0.35/0.60      (((k2_lattices @ sk_A @ sk_D_1 @ (k3_lattices @ sk_A @ sk_C_2 @ sk_B_2))
% 0.35/0.60         = (sk_D_1))),
% 0.35/0.60      inference('demod', [status(thm)], ['132', '148'])).
% 0.35/0.60  thf('150', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('151', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k4_lattices @ sk_A @ sk_D_1 @ X0)
% 0.35/0.60              = (k2_lattices @ sk_A @ sk_D_1 @ X0)))),
% 0.35/0.60      inference('clc', [status(thm)], ['100', '101'])).
% 0.35/0.60  thf('152', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_D_1 @ sk_C_2)
% 0.35/0.60         = (k2_lattices @ sk_A @ sk_D_1 @ sk_C_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['150', '151'])).
% 0.35/0.60  thf('153', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('154', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('155', plain,
% 0.35/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.35/0.60          | ~ (l1_lattices @ X5)
% 0.35/0.60          | ~ (v6_lattices @ X5)
% 0.35/0.60          | (v2_struct_0 @ X5)
% 0.35/0.60          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.35/0.60          | ((k4_lattices @ X5 @ X4 @ X6) = (k4_lattices @ X5 @ X6 @ X4)))),
% 0.35/0.60      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 0.35/0.60  thf('156', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60            = (k4_lattices @ sk_A @ X0 @ sk_C_2))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A)
% 0.35/0.60          | ~ (v6_lattices @ sk_A)
% 0.35/0.60          | ~ (l1_lattices @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['154', '155'])).
% 0.35/0.60  thf('157', plain, ((v6_lattices @ sk_A)),
% 0.35/0.60      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.35/0.60  thf('158', plain, ((l1_lattices @ sk_A)),
% 0.35/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.60  thf('159', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60            = (k4_lattices @ sk_A @ X0 @ sk_C_2))
% 0.35/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | (v2_struct_0 @ sk_A))),
% 0.35/0.60      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.35/0.60  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('161', plain,
% 0.35/0.60      (![X0 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.60          | ((k4_lattices @ sk_A @ sk_C_2 @ X0)
% 0.35/0.60              = (k4_lattices @ sk_A @ X0 @ sk_C_2)))),
% 0.35/0.60      inference('clc', [status(thm)], ['159', '160'])).
% 0.35/0.60  thf('162', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 0.35/0.60         = (k4_lattices @ sk_A @ sk_D_1 @ sk_C_2))),
% 0.35/0.60      inference('sup-', [status(thm)], ['153', '161'])).
% 0.35/0.60  thf('163', plain,
% 0.35/0.60      (((k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 0.35/0.60         = (k2_lattices @ sk_A @ sk_D_1 @ sk_C_2))),
% 0.35/0.60      inference('demod', [status(thm)], ['152', '162'])).
% 0.35/0.60  thf('164', plain,
% 0.35/0.60      (((sk_D_1)
% 0.35/0.60         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_2 @ sk_B_2) @ 
% 0.35/0.60            (k4_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 0.35/0.60      inference('demod', [status(thm)], ['124', '129', '149', '163'])).
% 0.35/0.60  thf('165', plain, (((sk_D_1) = (sk_C_2))),
% 0.35/0.60      inference('sup+', [status(thm)], ['89', '164'])).
% 0.35/0.60  thf('166', plain, (((sk_C_2) != (sk_D_1))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('167', plain, ($false),
% 0.35/0.60      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 0.35/0.60  
% 0.35/0.60  % SZS output end Refutation
% 0.35/0.60  
% 0.35/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
