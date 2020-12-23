%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5bBBmsrkES

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:38 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 535 expanded)
%              Number of leaves         :   35 ( 170 expanded)
%              Depth                    :   19
%              Number of atoms          : 1646 (8632 expanded)
%              Number of equality atoms :   55 (  62 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k7_lattices_type,type,(
    k7_lattices: $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

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

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(t53_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_lattices @ A @ B @ C )
               => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v17_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_lattices @ A @ B @ C )
                 => ( r3_lattices @ A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_lattices])).

thf('0',plain,(
    ~ ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_lattices,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X7 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X7 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(redefinition_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k2_lattices @ A @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ( l1_lattices @ X9 )
      | ~ ( l3_lattices @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('25',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','22','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
        = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
    = ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t21_lattices,axiom,(
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

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( ( k2_lattices @ X20 @ X19 @ X21 )
       != X19 )
      | ( r1_lattices @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v9_lattices @ X20 )
      | ~ ( v8_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
       != ( k7_lattices @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ( ( k2_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
       != ( k7_lattices @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['32','38','44','45'])).

thf('47',plain,
    ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
     != ( k7_lattices @ sk_A @ sk_C_1 ) )
    | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('49',plain,
    ( ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
     != ( k7_lattices @ sk_A @ sk_C_1 ) )
    | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
    | ( ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
     != ( k7_lattices @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) )
                = ( k4_lattices @ A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k7_lattices @ X23 @ ( k3_lattices @ X23 @ X22 @ X24 ) )
        = ( k4_lattices @ X23 @ ( k7_lattices @ X23 @ X22 ) @ ( k7_lattices @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v17_lattices @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t51_lattices])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C_1 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C_1 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C_1 @ X0 ) )
        = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k7_lattices @ sk_A @ ( k3_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('65',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X9: $i] :
      ( ( l2_lattices @ X9 )
      | ~ ( l3_lattices @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('75',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','72','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('82',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l2_lattices @ X11 )
      | ~ ( v4_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k3_lattices @ X11 @ X10 @ X12 )
        = ( k1_lattices @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('85',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k3_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k3_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v8_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k1_lattices @ X4 @ ( k2_lattices @ X4 @ X6 @ X5 ) @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l3_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_1 ) @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_1 ) @ sk_C_1 )
        = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_1 ) @ sk_C_1 )
        = sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('106',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_1 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['100','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_lattices @ X20 @ X19 @ X21 )
      | ( ( k2_lattices @ X20 @ X19 @ X21 )
        = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v9_lattices @ X20 )
      | ~ ( v8_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('117',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('118',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ~ ( r1_lattices @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','119'])).

thf('121',plain,(
    r3_lattices @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('123',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v9_lattices @ X17 )
      | ~ ( v8_lattices @ X17 )
      | ~ ( v6_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( r1_lattices @ X17 @ X16 @ X18 )
      | ~ ( r3_lattices @ X17 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('126',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('127',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('128',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B_1 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['121','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    r1_lattices @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_lattices @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('136',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k4_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k1_lattices @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['111','138'])).

thf('140',plain,
    ( sk_C_1
    = ( k3_lattices @ sk_A @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','139'])).

thf('141',plain,
    ( ( k7_lattices @ sk_A @ sk_C_1 )
    = ( k4_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['62','140'])).

thf('142',plain,
    ( ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) )
    | ( ( k7_lattices @ sk_A @ sk_C_1 )
     != ( k7_lattices @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','141'])).

thf('143',plain,(
    r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('145',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v9_lattices @ X17 )
      | ~ ( v8_lattices @ X17 )
      | ~ ( v6_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( r3_lattices @ X17 @ X16 @ X18 )
      | ~ ( r1_lattices @ X17 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('148',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('149',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('150',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['143','151'])).

thf('153',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C_1 ) @ ( k7_lattices @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['0','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5bBBmsrkES
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.05/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.28  % Solved by: fo/fo7.sh
% 1.05/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.28  % done 518 iterations in 0.796s
% 1.05/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.28  % SZS output start Refutation
% 1.05/1.28  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 1.05/1.28  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 1.05/1.28  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 1.05/1.28  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 1.05/1.28  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 1.05/1.28  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 1.05/1.28  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 1.05/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.28  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 1.05/1.28  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.05/1.28  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 1.05/1.28  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.05/1.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.05/1.28  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 1.05/1.28  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 1.05/1.28  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 1.05/1.28  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 1.05/1.28  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 1.05/1.28  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 1.05/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.28  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 1.05/1.28  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 1.05/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.28  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 1.05/1.28  thf(t53_lattices, conjecture,
% 1.05/1.28    (![A:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.05/1.28         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.05/1.28       ( ![B:$i]:
% 1.05/1.28         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28           ( ![C:$i]:
% 1.05/1.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28               ( ( r3_lattices @ A @ B @ C ) =>
% 1.05/1.28                 ( r3_lattices @
% 1.05/1.28                   A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ))).
% 1.05/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.28    (~( ![A:$i]:
% 1.05/1.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.05/1.28            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.05/1.28          ( ![B:$i]:
% 1.05/1.28            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28              ( ![C:$i]:
% 1.05/1.28                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28                  ( ( r3_lattices @ A @ B @ C ) =>
% 1.05/1.28                    ( r3_lattices @
% 1.05/1.28                      A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ) )),
% 1.05/1.28    inference('cnf.neg', [status(esa)], [t53_lattices])).
% 1.05/1.28  thf('0', plain,
% 1.05/1.28      (~ (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28          (k7_lattices @ sk_A @ sk_B_1))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(dt_k7_lattices, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 1.05/1.28         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.28       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 1.05/1.28  thf('2', plain,
% 1.05/1.28      (![X7 : $i, X8 : $i]:
% 1.05/1.28         (~ (l3_lattices @ X7)
% 1.05/1.28          | (v2_struct_0 @ X7)
% 1.05/1.28          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 1.05/1.28          | (m1_subset_1 @ (k7_lattices @ X7 @ X8) @ (u1_struct_0 @ X7)))),
% 1.05/1.28      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 1.05/1.28  thf('3', plain,
% 1.05/1.28      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.05/1.28        | (v2_struct_0 @ sk_A)
% 1.05/1.28        | ~ (l3_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.28  thf('4', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('5', plain,
% 1.05/1.28      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.05/1.28        | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['3', '4'])).
% 1.05/1.28  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('7', plain,
% 1.05/1.28      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('clc', [status(thm)], ['5', '6'])).
% 1.05/1.28  thf('8', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('9', plain,
% 1.05/1.28      (![X7 : $i, X8 : $i]:
% 1.05/1.28         (~ (l3_lattices @ X7)
% 1.05/1.28          | (v2_struct_0 @ X7)
% 1.05/1.28          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 1.05/1.28          | (m1_subset_1 @ (k7_lattices @ X7 @ X8) @ (u1_struct_0 @ X7)))),
% 1.05/1.28      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 1.05/1.28  thf('10', plain,
% 1.05/1.28      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 1.05/1.28        | (v2_struct_0 @ sk_A)
% 1.05/1.28        | ~ (l3_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.28  thf('11', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('12', plain,
% 1.05/1.28      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 1.05/1.28        | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.28  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('14', plain,
% 1.05/1.28      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('clc', [status(thm)], ['12', '13'])).
% 1.05/1.28  thf(redefinition_k4_lattices, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.05/1.28         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.05/1.28         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.28       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 1.05/1.28  thf('15', plain,
% 1.05/1.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.05/1.28          | ~ (l1_lattices @ X14)
% 1.05/1.28          | ~ (v6_lattices @ X14)
% 1.05/1.28          | (v2_struct_0 @ X14)
% 1.05/1.28          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 1.05/1.28          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 1.05/1.28      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 1.05/1.28  thf('16', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28            = (k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v6_lattices @ sk_A)
% 1.05/1.28          | ~ (l1_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['14', '15'])).
% 1.05/1.28  thf(cc1_lattices, axiom,
% 1.05/1.28    (![A:$i]:
% 1.05/1.28     ( ( l3_lattices @ A ) =>
% 1.05/1.28       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 1.05/1.28         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 1.05/1.28           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 1.05/1.28           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 1.05/1.28  thf('17', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ X0)
% 1.05/1.28          | ~ (v10_lattices @ X0)
% 1.05/1.28          | (v6_lattices @ X0)
% 1.05/1.28          | ~ (l3_lattices @ X0))),
% 1.05/1.28      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.05/1.28  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('19', plain,
% 1.05/1.28      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.28  thf('20', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('21', plain, ((v10_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('22', plain, ((v6_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.05/1.28  thf('23', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(dt_l3_lattices, axiom,
% 1.05/1.28    (![A:$i]:
% 1.05/1.28     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 1.05/1.28  thf('24', plain, (![X9 : $i]: ((l1_lattices @ X9) | ~ (l3_lattices @ X9))),
% 1.05/1.28      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 1.05/1.28  thf('25', plain, ((l1_lattices @ sk_A)),
% 1.05/1.28      inference('sup-', [status(thm)], ['23', '24'])).
% 1.05/1.28  thf('26', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28            = (k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['16', '22', '25'])).
% 1.05/1.28  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('28', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28              = (k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)))),
% 1.05/1.28      inference('clc', [status(thm)], ['26', '27'])).
% 1.05/1.28  thf('29', plain,
% 1.05/1.28      (((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28         (k7_lattices @ sk_A @ sk_B_1))
% 1.05/1.28         = (k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28            (k7_lattices @ sk_A @ sk_B_1)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['7', '28'])).
% 1.05/1.28  thf('30', plain,
% 1.05/1.28      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('clc', [status(thm)], ['12', '13'])).
% 1.05/1.28  thf(t21_lattices, axiom,
% 1.05/1.28    (![A:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 1.05/1.28         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.05/1.28       ( ![B:$i]:
% 1.05/1.28         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28           ( ![C:$i]:
% 1.05/1.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28               ( ( r1_lattices @ A @ B @ C ) <=>
% 1.05/1.28                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 1.05/1.28  thf('31', plain,
% 1.05/1.28      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.05/1.28          | ((k2_lattices @ X20 @ X19 @ X21) != (X19))
% 1.05/1.28          | (r1_lattices @ X20 @ X19 @ X21)
% 1.05/1.28          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 1.05/1.28          | ~ (l3_lattices @ X20)
% 1.05/1.28          | ~ (v9_lattices @ X20)
% 1.05/1.28          | ~ (v8_lattices @ X20)
% 1.05/1.28          | (v2_struct_0 @ X20))),
% 1.05/1.28      inference('cnf', [status(esa)], [t21_lattices])).
% 1.05/1.28  thf('32', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v8_lattices @ sk_A)
% 1.05/1.28          | ~ (v9_lattices @ sk_A)
% 1.05/1.28          | ~ (l3_lattices @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28          | ((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28              != (k7_lattices @ sk_A @ sk_C_1)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['30', '31'])).
% 1.05/1.28  thf('33', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ X0)
% 1.05/1.28          | ~ (v10_lattices @ X0)
% 1.05/1.28          | (v8_lattices @ X0)
% 1.05/1.28          | ~ (l3_lattices @ X0))),
% 1.05/1.28      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.05/1.28  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('35', plain,
% 1.05/1.28      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['33', '34'])).
% 1.05/1.28  thf('36', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('37', plain, ((v10_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('38', plain, ((v8_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.05/1.28  thf('39', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ X0)
% 1.05/1.28          | ~ (v10_lattices @ X0)
% 1.05/1.28          | (v9_lattices @ X0)
% 1.05/1.28          | ~ (l3_lattices @ X0))),
% 1.05/1.28      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.05/1.28  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('41', plain,
% 1.05/1.28      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.28  thf('42', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('43', plain, ((v10_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('44', plain, ((v9_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.05/1.28  thf('45', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('46', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28          | ((k2_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28              != (k7_lattices @ sk_A @ sk_C_1)))),
% 1.05/1.28      inference('demod', [status(thm)], ['32', '38', '44', '45'])).
% 1.05/1.28  thf('47', plain,
% 1.05/1.28      ((((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28          (k7_lattices @ sk_A @ sk_B_1)) != (k7_lattices @ sk_A @ sk_C_1))
% 1.05/1.28        | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28           (k7_lattices @ sk_A @ sk_B_1))
% 1.05/1.28        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.05/1.28        | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['29', '46'])).
% 1.05/1.28  thf('48', plain,
% 1.05/1.28      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('clc', [status(thm)], ['5', '6'])).
% 1.05/1.28  thf('49', plain,
% 1.05/1.28      ((((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28          (k7_lattices @ sk_A @ sk_B_1)) != (k7_lattices @ sk_A @ sk_C_1))
% 1.05/1.28        | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28           (k7_lattices @ sk_A @ sk_B_1))
% 1.05/1.28        | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['47', '48'])).
% 1.05/1.28  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('51', plain,
% 1.05/1.28      (((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28         (k7_lattices @ sk_A @ sk_B_1))
% 1.05/1.28        | ((k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28            (k7_lattices @ sk_A @ sk_B_1)) != (k7_lattices @ sk_A @ sk_C_1)))),
% 1.05/1.28      inference('clc', [status(thm)], ['49', '50'])).
% 1.05/1.28  thf('52', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('53', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(t51_lattices, axiom,
% 1.05/1.28    (![A:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.05/1.28         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.05/1.28       ( ![B:$i]:
% 1.05/1.28         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28           ( ![C:$i]:
% 1.05/1.28             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28               ( ( k7_lattices @ A @ ( k3_lattices @ A @ B @ C ) ) =
% 1.05/1.28                 ( k4_lattices @
% 1.05/1.28                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 1.05/1.28  thf('54', plain,
% 1.05/1.28      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 1.05/1.28          | ((k7_lattices @ X23 @ (k3_lattices @ X23 @ X22 @ X24))
% 1.05/1.28              = (k4_lattices @ X23 @ (k7_lattices @ X23 @ X22) @ 
% 1.05/1.28                 (k7_lattices @ X23 @ X24)))
% 1.05/1.28          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 1.05/1.28          | ~ (l3_lattices @ X23)
% 1.05/1.28          | ~ (v17_lattices @ X23)
% 1.05/1.28          | ~ (v10_lattices @ X23)
% 1.05/1.28          | (v2_struct_0 @ X23))),
% 1.05/1.28      inference('cnf', [status(esa)], [t51_lattices])).
% 1.05/1.28  thf('55', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v10_lattices @ sk_A)
% 1.05/1.28          | ~ (v17_lattices @ sk_A)
% 1.05/1.28          | ~ (l3_lattices @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C_1 @ X0))
% 1.05/1.28              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28                 (k7_lattices @ sk_A @ X0))))),
% 1.05/1.28      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.28  thf('56', plain, ((v10_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('57', plain, ((v17_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('58', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('59', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C_1 @ X0))
% 1.05/1.28              = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28                 (k7_lattices @ sk_A @ X0))))),
% 1.05/1.28      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 1.05/1.28  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('61', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C_1 @ X0))
% 1.05/1.28            = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28               (k7_lattices @ sk_A @ X0)))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.28      inference('clc', [status(thm)], ['59', '60'])).
% 1.05/1.28  thf('62', plain,
% 1.05/1.28      (((k7_lattices @ sk_A @ (k3_lattices @ sk_A @ sk_C_1 @ sk_B_1))
% 1.05/1.28         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28            (k7_lattices @ sk_A @ sk_B_1)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['52', '61'])).
% 1.05/1.28  thf('63', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('64', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(commutativity_k3_lattices, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 1.05/1.28         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.05/1.28         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.28       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 1.05/1.28  thf('65', plain,
% 1.05/1.28      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 1.05/1.28          | ~ (l2_lattices @ X2)
% 1.05/1.28          | ~ (v4_lattices @ X2)
% 1.05/1.28          | (v2_struct_0 @ X2)
% 1.05/1.28          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 1.05/1.28          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 1.05/1.28      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 1.05/1.28  thf('66', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28            = (k3_lattices @ sk_A @ X0 @ sk_B_1))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v4_lattices @ sk_A)
% 1.05/1.28          | ~ (l2_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['64', '65'])).
% 1.05/1.28  thf('67', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ X0)
% 1.05/1.28          | ~ (v10_lattices @ X0)
% 1.05/1.28          | (v4_lattices @ X0)
% 1.05/1.28          | ~ (l3_lattices @ X0))),
% 1.05/1.28      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.05/1.28  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('69', plain,
% 1.05/1.28      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['67', '68'])).
% 1.05/1.28  thf('70', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('71', plain, ((v10_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('72', plain, ((v4_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.05/1.28  thf('73', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('74', plain, (![X9 : $i]: ((l2_lattices @ X9) | ~ (l3_lattices @ X9))),
% 1.05/1.28      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 1.05/1.28  thf('75', plain, ((l2_lattices @ sk_A)),
% 1.05/1.28      inference('sup-', [status(thm)], ['73', '74'])).
% 1.05/1.28  thf('76', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28            = (k3_lattices @ sk_A @ X0 @ sk_B_1))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['66', '72', '75'])).
% 1.05/1.28  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('78', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28              = (k3_lattices @ sk_A @ X0 @ sk_B_1)))),
% 1.05/1.28      inference('clc', [status(thm)], ['76', '77'])).
% 1.05/1.28  thf('79', plain,
% 1.05/1.28      (((k3_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.05/1.28         = (k3_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 1.05/1.28      inference('sup-', [status(thm)], ['63', '78'])).
% 1.05/1.28  thf('80', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('81', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(redefinition_k3_lattices, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 1.05/1.28         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.05/1.28         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.28       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 1.05/1.28  thf('82', plain,
% 1.05/1.28      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 1.05/1.28          | ~ (l2_lattices @ X11)
% 1.05/1.28          | ~ (v4_lattices @ X11)
% 1.05/1.28          | (v2_struct_0 @ X11)
% 1.05/1.28          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 1.05/1.28          | ((k3_lattices @ X11 @ X10 @ X12) = (k1_lattices @ X11 @ X10 @ X12)))),
% 1.05/1.28      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 1.05/1.28  thf('83', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v4_lattices @ sk_A)
% 1.05/1.28          | ~ (l2_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['81', '82'])).
% 1.05/1.28  thf('84', plain, ((v4_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.05/1.28  thf('85', plain, ((l2_lattices @ sk_A)),
% 1.05/1.28      inference('sup-', [status(thm)], ['73', '74'])).
% 1.05/1.28  thf('86', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28            = (k1_lattices @ sk_A @ sk_B_1 @ X0))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.05/1.28  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('88', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28              = (k1_lattices @ sk_A @ sk_B_1 @ X0)))),
% 1.05/1.28      inference('clc', [status(thm)], ['86', '87'])).
% 1.05/1.28  thf('89', plain,
% 1.05/1.28      (((k3_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.05/1.28         = (k1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.05/1.28      inference('sup-', [status(thm)], ['80', '88'])).
% 1.05/1.28  thf('90', plain,
% 1.05/1.28      (((k1_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.05/1.28         = (k3_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 1.05/1.28      inference('demod', [status(thm)], ['79', '89'])).
% 1.05/1.28  thf('91', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('92', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(d8_lattices, axiom,
% 1.05/1.28    (![A:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.05/1.28       ( ( v8_lattices @ A ) <=>
% 1.05/1.28         ( ![B:$i]:
% 1.05/1.28           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28             ( ![C:$i]:
% 1.05/1.28               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.28                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 1.05/1.28                   ( C ) ) ) ) ) ) ) ))).
% 1.05/1.28  thf('93', plain,
% 1.05/1.28      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.05/1.28         (~ (v8_lattices @ X4)
% 1.05/1.28          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 1.05/1.28          | ((k1_lattices @ X4 @ (k2_lattices @ X4 @ X6 @ X5) @ X5) = (X5))
% 1.05/1.28          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 1.05/1.28          | ~ (l3_lattices @ X4)
% 1.05/1.28          | (v2_struct_0 @ X4))),
% 1.05/1.28      inference('cnf', [status(esa)], [d8_lattices])).
% 1.05/1.28  thf('94', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (l3_lattices @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_1) @ sk_C_1)
% 1.05/1.28              = (sk_C_1))
% 1.05/1.28          | ~ (v8_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['92', '93'])).
% 1.05/1.28  thf('95', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('96', plain, ((v8_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.05/1.28  thf('97', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_1) @ sk_C_1)
% 1.05/1.28              = (sk_C_1)))),
% 1.05/1.28      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.05/1.28  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('99', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_1) @ sk_C_1)
% 1.05/1.28            = (sk_C_1))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.28      inference('clc', [status(thm)], ['97', '98'])).
% 1.05/1.28  thf('100', plain,
% 1.05/1.28      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ sk_C_1)
% 1.05/1.28         = (sk_C_1))),
% 1.05/1.28      inference('sup-', [status(thm)], ['91', '99'])).
% 1.05/1.28  thf('101', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('102', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('103', plain,
% 1.05/1.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.05/1.28          | ~ (l1_lattices @ X14)
% 1.05/1.28          | ~ (v6_lattices @ X14)
% 1.05/1.28          | (v2_struct_0 @ X14)
% 1.05/1.28          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 1.05/1.28          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 1.05/1.28      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 1.05/1.28  thf('104', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v6_lattices @ sk_A)
% 1.05/1.28          | ~ (l1_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['102', '103'])).
% 1.05/1.28  thf('105', plain, ((v6_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.05/1.28  thf('106', plain, ((l1_lattices @ sk_A)),
% 1.05/1.28      inference('sup-', [status(thm)], ['23', '24'])).
% 1.05/1.28  thf('107', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28            = (k2_lattices @ sk_A @ sk_B_1 @ X0))
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.05/1.28  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('109', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k4_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28              = (k2_lattices @ sk_A @ sk_B_1 @ X0)))),
% 1.05/1.28      inference('clc', [status(thm)], ['107', '108'])).
% 1.05/1.28  thf('110', plain,
% 1.05/1.28      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.05/1.28         = (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.05/1.28      inference('sup-', [status(thm)], ['101', '109'])).
% 1.05/1.28  thf('111', plain,
% 1.05/1.28      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B_1 @ sk_C_1) @ sk_C_1)
% 1.05/1.28         = (sk_C_1))),
% 1.05/1.28      inference('demod', [status(thm)], ['100', '110'])).
% 1.05/1.28  thf('112', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('113', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('114', plain,
% 1.05/1.28      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.05/1.28          | ~ (r1_lattices @ X20 @ X19 @ X21)
% 1.05/1.28          | ((k2_lattices @ X20 @ X19 @ X21) = (X19))
% 1.05/1.28          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 1.05/1.28          | ~ (l3_lattices @ X20)
% 1.05/1.28          | ~ (v9_lattices @ X20)
% 1.05/1.28          | ~ (v8_lattices @ X20)
% 1.05/1.28          | (v2_struct_0 @ X20))),
% 1.05/1.28      inference('cnf', [status(esa)], [t21_lattices])).
% 1.05/1.28  thf('115', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v8_lattices @ sk_A)
% 1.05/1.28          | ~ (v9_lattices @ sk_A)
% 1.05/1.28          | ~ (l3_lattices @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) = (sk_B_1))
% 1.05/1.28          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 1.05/1.28      inference('sup-', [status(thm)], ['113', '114'])).
% 1.05/1.28  thf('116', plain, ((v8_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.05/1.28  thf('117', plain, ((v9_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.05/1.28  thf('118', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('119', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         ((v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | ((k2_lattices @ sk_A @ sk_B_1 @ X0) = (sk_B_1))
% 1.05/1.28          | ~ (r1_lattices @ sk_A @ sk_B_1 @ X0))),
% 1.05/1.28      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 1.05/1.28  thf('120', plain,
% 1.05/1.28      ((~ (r1_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.05/1.28        | ((k2_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))
% 1.05/1.28        | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['112', '119'])).
% 1.05/1.28  thf('121', plain, ((r3_lattices @ sk_A @ sk_B_1 @ sk_C_1)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('122', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(redefinition_r3_lattices, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 1.05/1.28         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 1.05/1.28         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 1.05/1.28         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.28       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 1.05/1.28  thf('123', plain,
% 1.05/1.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.05/1.28          | ~ (l3_lattices @ X17)
% 1.05/1.28          | ~ (v9_lattices @ X17)
% 1.05/1.28          | ~ (v8_lattices @ X17)
% 1.05/1.28          | ~ (v6_lattices @ X17)
% 1.05/1.28          | (v2_struct_0 @ X17)
% 1.05/1.28          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 1.05/1.28          | (r1_lattices @ X17 @ X16 @ X18)
% 1.05/1.28          | ~ (r3_lattices @ X17 @ X16 @ X18))),
% 1.05/1.28      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 1.05/1.28  thf('124', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v6_lattices @ sk_A)
% 1.05/1.28          | ~ (v8_lattices @ sk_A)
% 1.05/1.28          | ~ (v9_lattices @ sk_A)
% 1.05/1.28          | ~ (l3_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['122', '123'])).
% 1.05/1.28  thf('125', plain, ((v6_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.05/1.28  thf('126', plain, ((v8_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.05/1.28  thf('127', plain, ((v9_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.05/1.28  thf('128', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('129', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (r3_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28          | (r1_lattices @ sk_A @ sk_B_1 @ X0)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 1.05/1.28  thf('130', plain,
% 1.05/1.28      (((v2_struct_0 @ sk_A)
% 1.05/1.28        | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 1.05/1.28        | (r1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.05/1.28      inference('sup-', [status(thm)], ['121', '129'])).
% 1.05/1.28  thf('131', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('132', plain,
% 1.05/1.28      (((v2_struct_0 @ sk_A) | (r1_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.05/1.28      inference('demod', [status(thm)], ['130', '131'])).
% 1.05/1.28  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('134', plain, ((r1_lattices @ sk_A @ sk_B_1 @ sk_C_1)),
% 1.05/1.28      inference('clc', [status(thm)], ['132', '133'])).
% 1.05/1.28  thf('135', plain,
% 1.05/1.28      (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1)
% 1.05/1.28         = (k2_lattices @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.05/1.28      inference('sup-', [status(thm)], ['101', '109'])).
% 1.05/1.28  thf('136', plain,
% 1.05/1.28      ((((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))
% 1.05/1.28        | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['120', '134', '135'])).
% 1.05/1.28  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('138', plain, (((k4_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.05/1.28      inference('clc', [status(thm)], ['136', '137'])).
% 1.05/1.28  thf('139', plain, (((k1_lattices @ sk_A @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.05/1.28      inference('demod', [status(thm)], ['111', '138'])).
% 1.05/1.28  thf('140', plain, (((sk_C_1) = (k3_lattices @ sk_A @ sk_C_1 @ sk_B_1))),
% 1.05/1.28      inference('demod', [status(thm)], ['90', '139'])).
% 1.05/1.28  thf('141', plain,
% 1.05/1.28      (((k7_lattices @ sk_A @ sk_C_1)
% 1.05/1.28         = (k4_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28            (k7_lattices @ sk_A @ sk_B_1)))),
% 1.05/1.28      inference('demod', [status(thm)], ['62', '140'])).
% 1.05/1.28  thf('142', plain,
% 1.05/1.28      (((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28         (k7_lattices @ sk_A @ sk_B_1))
% 1.05/1.28        | ((k7_lattices @ sk_A @ sk_C_1) != (k7_lattices @ sk_A @ sk_C_1)))),
% 1.05/1.28      inference('demod', [status(thm)], ['51', '141'])).
% 1.05/1.28  thf('143', plain,
% 1.05/1.28      ((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28        (k7_lattices @ sk_A @ sk_B_1))),
% 1.05/1.28      inference('simplify', [status(thm)], ['142'])).
% 1.05/1.28  thf('144', plain,
% 1.05/1.28      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('clc', [status(thm)], ['12', '13'])).
% 1.05/1.28  thf('145', plain,
% 1.05/1.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.05/1.28         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 1.05/1.28          | ~ (l3_lattices @ X17)
% 1.05/1.28          | ~ (v9_lattices @ X17)
% 1.05/1.28          | ~ (v8_lattices @ X17)
% 1.05/1.28          | ~ (v6_lattices @ X17)
% 1.05/1.28          | (v2_struct_0 @ X17)
% 1.05/1.28          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 1.05/1.28          | (r3_lattices @ X17 @ X16 @ X18)
% 1.05/1.28          | ~ (r1_lattices @ X17 @ X16 @ X18))),
% 1.05/1.28      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 1.05/1.28  thf('146', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A)
% 1.05/1.28          | ~ (v6_lattices @ sk_A)
% 1.05/1.28          | ~ (v8_lattices @ sk_A)
% 1.05/1.28          | ~ (v9_lattices @ sk_A)
% 1.05/1.28          | ~ (l3_lattices @ sk_A))),
% 1.05/1.28      inference('sup-', [status(thm)], ['144', '145'])).
% 1.05/1.28  thf('147', plain, ((v6_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.05/1.28  thf('148', plain, ((v8_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.05/1.28  thf('149', plain, ((v9_lattices @ sk_A)),
% 1.05/1.28      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.05/1.28  thf('150', plain, ((l3_lattices @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('151', plain,
% 1.05/1.28      (![X0 : $i]:
% 1.05/1.28         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ X0)
% 1.05/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.28          | (v2_struct_0 @ sk_A))),
% 1.05/1.28      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 1.05/1.28  thf('152', plain,
% 1.05/1.28      (((v2_struct_0 @ sk_A)
% 1.05/1.28        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.05/1.28        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28           (k7_lattices @ sk_A @ sk_B_1)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['143', '151'])).
% 1.05/1.28  thf('153', plain,
% 1.05/1.28      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.05/1.28      inference('clc', [status(thm)], ['5', '6'])).
% 1.05/1.28  thf('154', plain,
% 1.05/1.28      (((v2_struct_0 @ sk_A)
% 1.05/1.28        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28           (k7_lattices @ sk_A @ sk_B_1)))),
% 1.05/1.28      inference('demod', [status(thm)], ['152', '153'])).
% 1.05/1.28  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf('156', plain,
% 1.05/1.28      ((r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C_1) @ 
% 1.05/1.28        (k7_lattices @ sk_A @ sk_B_1))),
% 1.05/1.28      inference('clc', [status(thm)], ['154', '155'])).
% 1.05/1.28  thf('157', plain, ($false), inference('demod', [status(thm)], ['0', '156'])).
% 1.05/1.28  
% 1.05/1.28  % SZS output end Refutation
% 1.05/1.28  
% 1.05/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
