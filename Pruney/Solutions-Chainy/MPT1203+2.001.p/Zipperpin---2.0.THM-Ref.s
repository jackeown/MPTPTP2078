%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qzIl6vuyGq

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:32 EST 2020

% Result     : Theorem 31.19s
% Output     : Refutation 31.19s
% Verified   : 
% Statistics : Number of formulae       :  448 (3030 expanded)
%              Number of leaves         :   36 ( 887 expanded)
%              Depth                    :   22
%              Number of atoms          : 4266 (66038 expanded)
%              Number of equality atoms :  233 (4236 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v11_lattices_type,type,(
    v11_lattices: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_lattices @ X22 )
      | ~ ( v6_lattices @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X22 @ X21 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattices])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('13',plain,(
    ! [X24: $i] :
      ( ( l1_lattices @ X24 )
      | ~ ( l3_lattices @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('14',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','11','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','17'])).

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

thf('19',plain,(
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

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) )
      | ~ ( v11_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v11_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r1_lattices @ X34 @ X33 @ X35 )
      | ( ( k2_lattices @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l3_lattices @ X34 )
      | ~ ( v9_lattices @ X34 )
      | ~ ( v8_lattices @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_3 @ X0 )
        = sk_B_3 )
      | ~ ( r1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_3 @ X0 )
        = sk_B_3 )
      | ~ ( r1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','33','39','40'])).

thf('42',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    | ( ( k2_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
      = sk_B_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( ( k1_lattices @ X12 @ X11 @ X13 )
       != X13 )
      | ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l2_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_3 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_3 @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X24: $i] :
      ( ( l2_lattices @ X24 )
      | ~ ( l3_lattices @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('49',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_3 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_B_3 @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ( k1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
     != sk_B_3 )
    | ( r1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    | ( ( k1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
     != sk_B_3 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l2_lattices @ X26 )
      | ~ ( v4_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( ( k3_lattices @ X26 @ X25 @ X27 )
        = ( k1_lattices @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('69',plain,
    ( ( r1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
     != sk_B_3 ) ),
    inference(demod,[status(thm)],['53','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('71',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( ( k1_lattices @ X32 @ X31 @ X31 )
        = X31 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v9_lattices @ X32 )
      | ~ ( v8_lattices @ X32 )
      | ~ ( v6_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_lattices])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
      = sk_B_3 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('74',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('75',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('76',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
      = sk_B_3 ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    = sk_B_3 ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    | ( sk_B_3 != sk_B_3 ) ),
    inference(demod,[status(thm)],['69','80'])).

thf('82',plain,(
    r1_lattices @ sk_A @ sk_B_3 @ sk_B_3 ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('85',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_lattices @ X29 )
      | ~ ( v6_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( ( k4_lattices @ X29 @ X28 @ X30 )
        = ( k2_lattices @ X29 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('88',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
      = sk_B_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','82','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    = sk_B_3 ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_B_3 )
    = sk_B_3 ),
    inference(clc,[status(thm)],['93','94'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['23','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_lattices @ X29 )
      | ~ ( v6_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( ( k4_lattices @ X29 @ X28 @ X30 )
        = ( k2_lattices @ X29 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('104',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['0','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('115',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_D_2 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k3_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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

thf('119',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('122',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k3_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['116','126'])).

thf('128',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['115','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
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

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_C_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) )
      | ~ ( v11_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v11_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_C_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('140',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r1_lattices @ X34 @ X33 @ X35 )
      | ( ( k2_lattices @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l3_lattices @ X34 )
      | ~ ( v9_lattices @ X34 )
      | ~ ( v8_lattices @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_3 @ X0 )
        = sk_C_3 )
      | ~ ( r1_lattices @ sk_A @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('146',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('147',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_3 @ X0 )
        = sk_C_3 )
      | ~ ( r1_lattices @ sk_A @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    | ( ( k2_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
      = sk_C_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( ( k1_lattices @ X12 @ X11 @ X13 )
       != X13 )
      | ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l2_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_C_3 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_C_3 @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_C_3 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_C_3 @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
     != sk_C_3 )
    | ( r1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( r1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    | ( ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
     != sk_C_3 ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l2_lattices @ X26 )
      | ~ ( v4_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( ( k3_lattices @ X26 @ X25 @ X27 )
        = ( k1_lattices @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('164',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['159','167'])).

thf('169',plain,
    ( ( r1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    | ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
     != sk_C_3 ) ),
    inference(demod,[status(thm)],['158','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( ( k1_lattices @ X32 @ X31 @ X31 )
        = X31 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v9_lattices @ X32 )
      | ~ ( v8_lattices @ X32 )
      | ~ ( v6_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_lattices])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
      = sk_C_3 ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('174',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('175',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('176',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = ( k1_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['159','167'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
      = sk_C_3 ) ),
    inference(demod,[status(thm)],['172','173','174','175','176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = sk_C_3 ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( r1_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    | ( sk_C_3 != sk_C_3 ) ),
    inference(demod,[status(thm)],['169','180'])).

thf('182',plain,(
    r1_lattices @ sk_A @ sk_C_3 @ sk_C_3 ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('184',plain,
    ( ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
      = sk_C_3 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['149','182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_C_3 )
    = sk_C_3 ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,
    ( sk_C_3
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['140','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_C_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_C_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k1_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_C_3 @ ( k2_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['129','190'])).

thf('192',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('194',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k1_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('196',plain,
    ( ( k2_lattices @ sk_A @ sk_C_3 @ ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_C_3 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['191','194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_3 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('199',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
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

thf('202',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( ( k4_lattices @ X5 @ X4 @ X6 )
        = ( k4_lattices @ X5 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('205',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['200','208'])).

thf('210',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['199','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('212',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_C_3 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['199','209'])).

thf('215',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l2_lattices @ X26 )
      | ~ ( v4_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( ( k3_lattices @ X26 @ X25 @ X27 )
        = ( k1_lattices @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('218',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_C_3 )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['213','221'])).

thf('223',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['199','209'])).

thf('224',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('228',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_C_3 ) ) ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['223','231'])).

thf('233',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_C_3 ) ),
    inference(demod,[status(thm)],['222','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
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

thf('236',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v8_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( ( k1_lattices @ X18 @ ( k2_lattices @ X18 @ X20 @ X19 ) @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ sk_C_3 )
        = sk_C_3 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ sk_C_3 )
        = sk_C_3 ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_3 ) @ sk_C_3 )
        = sk_C_3 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) @ sk_C_3 )
    = sk_C_3 ),
    inference('sup-',[status(thm)],['234','242'])).

thf('244',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('246',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['200','208'])).

thf('248',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_C_3 )
    = sk_C_3 ),
    inference(demod,[status(thm)],['243','248'])).

thf('250',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = sk_C_3 ),
    inference('sup+',[status(thm)],['233','249'])).

thf('251',plain,
    ( sk_C_3
    = ( k1_lattices @ sk_A @ sk_C_3 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['212','250'])).

thf('252',plain,
    ( sk_C_3
    = ( k2_lattices @ sk_A @ sk_C_3 @ ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference('sup+',[status(thm)],['196','251'])).

thf('253',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_C_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('255',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_2 )
    = ( k2_lattices @ sk_A @ sk_C_3 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,
    ( sk_C_3
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['112','128','252','255'])).

thf('257',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_B_3 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['23','95','96'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_lattices @ X29 )
      | ~ ( v6_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( ( k4_lattices @ X29 @ X28 @ X30 )
        = ( k2_lattices @ X29 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('264',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('266',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,
    ( ( k4_lattices @ sk_A @ sk_D_2 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['261','269'])).

thf('271',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['200','208'])).

thf('273',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('276',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_2 )
    = ( k4_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k4_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['273','276'])).

thf('278',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['270','277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['260','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k2_lattices @ sk_A @ sk_D_2 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['257','281'])).

thf('283',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k1_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('285',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_C_3 )
    = ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('287',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k1_lattices @ sk_A @ sk_B_3 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
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

thf('292',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_D_2 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_2 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) )
      | ~ ( v11_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v11_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ sk_D_2 @ X1 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_2 ) @ ( k2_lattices @ sk_A @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_D_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_D_2 @ sk_D_2 ) @ ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['289','295'])).

thf('297',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('299',plain,
    ( ( k4_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r1_lattices @ X34 @ X33 @ X35 )
      | ( ( k2_lattices @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l3_lattices @ X34 )
      | ~ ( v9_lattices @ X34 )
      | ~ ( v8_lattices @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_2 @ X0 )
        = sk_D_2 )
      | ~ ( r1_lattices @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('305',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('306',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_2 @ X0 )
        = sk_D_2 )
      | ~ ( r1_lattices @ sk_A @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['303','304','305','306'])).

thf('308',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    | ( ( k2_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
      = sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['300','307'])).

thf('309',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( ( k1_lattices @ X12 @ X11 @ X13 )
       != X13 )
      | ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l2_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_D_2 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_D_2 @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('314',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_D_2 @ X0 )
      | ( ( k1_lattices @ sk_A @ sk_D_2 @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['312','313'])).

thf('315',plain,
    ( ( ( k1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
     != sk_D_2 )
    | ( r1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['309','314'])).

thf('316',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,
    ( ( r1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    | ( ( k1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
     != sk_D_2 ) ),
    inference(clc,[status(thm)],['315','316'])).

thf('318',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( ( k1_lattices @ X32 @ X31 @ X31 )
        = X31 )
      | ~ ( l3_lattices @ X32 )
      | ~ ( v9_lattices @ X32 )
      | ~ ( v8_lattices @ X32 )
      | ~ ( v6_lattices @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t17_lattices])).

thf('320',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
      = sk_D_2 ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('322',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('323',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('324',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
      = sk_D_2 ) ),
    inference(demod,[status(thm)],['320','321','322','323','324'])).

thf('326',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,
    ( ( k1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    = sk_D_2 ),
    inference(clc,[status(thm)],['325','326'])).

thf('328',plain,
    ( ( r1_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    | ( sk_D_2 != sk_D_2 ) ),
    inference(demod,[status(thm)],['317','327'])).

thf('329',plain,(
    r1_lattices @ sk_A @ sk_D_2 @ sk_D_2 ),
    inference(simplify,[status(thm)],['328'])).

thf('330',plain,
    ( ( k4_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('331',plain,
    ( ( ( k4_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
      = sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['308','329','330'])).

thf('332',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( k4_lattices @ sk_A @ sk_D_2 @ sk_D_2 )
    = sk_D_2 ),
    inference(clc,[status(thm)],['331','332'])).

thf('334',plain,
    ( sk_D_2
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['299','333'])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_D_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_D_2 @ ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['296','334'])).

thf('336',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_D_2 @ X0 ) )
        = ( k1_lattices @ sk_A @ sk_D_2 @ ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['335','336'])).

thf('338',plain,
    ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k1_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_D_2 @ ( k2_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['288','337'])).

thf('339',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l2_lattices @ X26 )
      | ~ ( v4_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( ( k3_lattices @ X26 @ X25 @ X27 )
        = ( k1_lattices @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('342',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('344',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('345',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['342','343','344'])).

thf('346',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_D_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('348',plain,
    ( ( k3_lattices @ sk_A @ sk_D_2 @ sk_B_3 )
    = ( k1_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['339','347'])).

thf('349',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k3_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['116','126'])).

thf('350',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('352',plain,
    ( ( k3_lattices @ sk_A @ sk_B_3 @ sk_D_2 )
    = ( k3_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['350','351'])).

thf('353',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k3_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference('sup+',[status(thm)],['349','352'])).

thf('354',plain,
    ( ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k1_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['348','353'])).

thf('355',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['270','277'])).

thf('356',plain,
    ( ( k2_lattices @ sk_A @ sk_D_2 @ ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_D_2 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['338','354','355'])).

thf('357',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['199','209'])).

thf('358',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k1_lattices @ sk_A @ sk_D_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['345','346'])).

thf('359',plain,
    ( ( k3_lattices @ sk_A @ sk_D_2 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ sk_D_2 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['357','358'])).

thf('360',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('362',plain,
    ( ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_D_2 )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['360','361'])).

thf('363',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['199','209'])).

thf('364',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('366',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('368',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('369',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['366','367','368'])).

thf('370',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ sk_D_2 ) ) ) ),
    inference(clc,[status(thm)],['369','370'])).

thf('372',plain,
    ( ( k3_lattices @ sk_A @ sk_D_2 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k3_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['363','371'])).

thf('373',plain,
    ( ( k3_lattices @ sk_A @ sk_D_2 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['362','372'])).

thf('374',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v8_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( ( k1_lattices @ X18 @ ( k2_lattices @ X18 @ X20 @ X19 ) @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('377',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_2 ) @ sk_D_2 )
        = sk_D_2 )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['375','376'])).

thf('378',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('380',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_2 ) @ sk_D_2 )
        = sk_D_2 ) ) ),
    inference(demod,[status(thm)],['377','378','379'])).

thf('381',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_D_2 ) @ sk_D_2 )
        = sk_D_2 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['380','381'])).

thf('383',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) @ sk_D_2 )
    = sk_D_2 ),
    inference('sup-',[status(thm)],['374','382'])).

thf('384',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B_3 @ X0 )
        = ( k2_lattices @ sk_A @ sk_B_3 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('386',plain,
    ( ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_2 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['384','385'])).

thf('387',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k4_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('388',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 )
    = ( k2_lattices @ sk_A @ sk_B_3 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['386','387'])).

thf('389',plain,
    ( ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ sk_D_2 )
    = sk_D_2 ),
    inference(demod,[status(thm)],['383','388'])).

thf('390',plain,
    ( ( k3_lattices @ sk_A @ sk_D_2 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) )
    = sk_D_2 ),
    inference('sup+',[status(thm)],['373','389'])).

thf('391',plain,
    ( sk_D_2
    = ( k1_lattices @ sk_A @ sk_D_2 @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['359','390'])).

thf('392',plain,
    ( sk_D_2
    = ( k2_lattices @ sk_A @ sk_D_2 @ ( k3_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) ) ),
    inference('sup+',[status(thm)],['356','391'])).

thf('393',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_D_2 @ X0 )
        = ( k2_lattices @ sk_A @ sk_D_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('395',plain,
    ( ( k4_lattices @ sk_A @ sk_D_2 @ sk_C_3 )
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['393','394'])).

thf('396',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,(
    m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ~ ( v6_lattices @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( ( k4_lattices @ X5 @ X4 @ X6 )
        = ( k4_lattices @ X5 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('399',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['397','398'])).

thf('400',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('401',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('402',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['399','400','401'])).

thf('403',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_C_3 @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ sk_C_3 ) ) ) ),
    inference(clc,[status(thm)],['402','403'])).

thf('405',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_2 )
    = ( k4_lattices @ sk_A @ sk_D_2 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['396','404'])).

thf('406',plain,
    ( ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_2 )
    = ( k2_lattices @ sk_A @ sk_D_2 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['395','405'])).

thf('407',plain,
    ( sk_D_2
    = ( k1_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_B_3 ) @ ( k4_lattices @ sk_A @ sk_C_3 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['282','287','392','406'])).

thf('408',plain,(
    sk_D_2 = sk_C_3 ),
    inference('sup+',[status(thm)],['256','407'])).

thf('409',plain,(
    sk_C_3 != sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['408','409'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qzIl6vuyGq
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 31.19/31.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 31.19/31.41  % Solved by: fo/fo7.sh
% 31.19/31.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.19/31.41  % done 3942 iterations in 30.943s
% 31.19/31.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 31.19/31.41  % SZS output start Refutation
% 31.19/31.41  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 31.19/31.41  thf(sk_B_3_type, type, sk_B_3: $i).
% 31.19/31.41  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 31.19/31.41  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 31.19/31.41  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 31.19/31.41  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 31.19/31.41  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 31.19/31.41  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 31.19/31.41  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 31.19/31.41  thf(sk_C_3_type, type, sk_C_3: $i).
% 31.19/31.41  thf(v11_lattices_type, type, v11_lattices: $i > $o).
% 31.19/31.41  thf(sk_D_2_type, type, sk_D_2: $i).
% 31.19/31.41  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 31.19/31.41  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 31.19/31.41  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 31.19/31.41  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 31.19/31.41  thf(sk_A_type, type, sk_A: $i).
% 31.19/31.41  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 31.19/31.41  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 31.19/31.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 31.19/31.41  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 31.19/31.41  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 31.19/31.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.19/31.41  thf(t32_lattices, conjecture,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 31.19/31.41         ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 31.19/31.41       ( ![B:$i]:
% 31.19/31.41         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41           ( ![C:$i]:
% 31.19/31.41             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41               ( ![D:$i]:
% 31.19/31.41                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41                   ( ( ( ( k4_lattices @ A @ B @ C ) =
% 31.19/31.41                         ( k4_lattices @ A @ B @ D ) ) & 
% 31.19/31.41                       ( ( k3_lattices @ A @ B @ C ) =
% 31.19/31.41                         ( k3_lattices @ A @ B @ D ) ) ) =>
% 31.19/31.41                     ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ))).
% 31.19/31.41  thf(zf_stmt_0, negated_conjecture,
% 31.19/31.41    (~( ![A:$i]:
% 31.19/31.41        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 31.19/31.41            ( v11_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 31.19/31.41          ( ![B:$i]:
% 31.19/31.41            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41              ( ![C:$i]:
% 31.19/31.41                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41                  ( ![D:$i]:
% 31.19/31.41                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41                      ( ( ( ( k4_lattices @ A @ B @ C ) =
% 31.19/31.41                            ( k4_lattices @ A @ B @ D ) ) & 
% 31.19/31.41                          ( ( k3_lattices @ A @ B @ C ) =
% 31.19/31.41                            ( k3_lattices @ A @ B @ D ) ) ) =>
% 31.19/31.41                        ( ( C ) = ( D ) ) ) ) ) ) ) ) ) ) )),
% 31.19/31.41    inference('cnf.neg', [status(esa)], [t32_lattices])).
% 31.19/31.41  thf('0', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('1', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('2', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('3', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(dt_k4_lattices, axiom,
% 31.19/31.41    (![A:$i,B:$i,C:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 31.19/31.41         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 31.19/31.41         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 31.19/31.41       ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 31.19/31.41  thf('4', plain,
% 31.19/31.41      (![X21 : $i, X22 : $i, X23 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 31.19/31.41          | ~ (l1_lattices @ X22)
% 31.19/31.41          | ~ (v6_lattices @ X22)
% 31.19/31.41          | (v2_struct_0 @ X22)
% 31.19/31.41          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 31.19/31.41          | (m1_subset_1 @ (k4_lattices @ X22 @ X21 @ X23) @ 
% 31.19/31.41             (u1_struct_0 @ X22)))),
% 31.19/31.41      inference('cnf', [status(esa)], [dt_k4_lattices])).
% 31.19/31.41  thf('5', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_3 @ X0) @ 
% 31.19/31.41           (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v6_lattices @ sk_A)
% 31.19/31.41          | ~ (l1_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['3', '4'])).
% 31.19/31.41  thf(cc1_lattices, axiom,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( l3_lattices @ A ) =>
% 31.19/31.41       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 31.19/31.41         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 31.19/31.41           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 31.19/31.41           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 31.19/31.41  thf('6', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ X0)
% 31.19/31.41          | ~ (v10_lattices @ X0)
% 31.19/31.41          | (v6_lattices @ X0)
% 31.19/31.41          | ~ (l3_lattices @ X0))),
% 31.19/31.41      inference('cnf', [status(esa)], [cc1_lattices])).
% 31.19/31.41  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('8', plain,
% 31.19/31.41      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['6', '7'])).
% 31.19/31.41  thf('9', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('10', plain, ((v10_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('11', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('12', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(dt_l3_lattices, axiom,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 31.19/31.41  thf('13', plain,
% 31.19/31.41      (![X24 : $i]: ((l1_lattices @ X24) | ~ (l3_lattices @ X24))),
% 31.19/31.41      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 31.19/31.41  thf('14', plain, ((l1_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['12', '13'])).
% 31.19/31.41  thf('15', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_3 @ X0) @ 
% 31.19/31.41           (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['5', '11', '14'])).
% 31.19/31.41  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('17', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_3 @ X0) @ 
% 31.19/31.41             (u1_struct_0 @ sk_A)))),
% 31.19/31.41      inference('clc', [status(thm)], ['15', '16'])).
% 31.19/31.41  thf('18', plain,
% 31.19/31.41      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_3 @ sk_B_3) @ 
% 31.19/31.41        (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['2', '17'])).
% 31.19/31.41  thf(d11_lattices, axiom,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 31.19/31.41       ( ( v11_lattices @ A ) <=>
% 31.19/31.41         ( ![B:$i]:
% 31.19/31.41           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41             ( ![C:$i]:
% 31.19/31.41               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41                 ( ![D:$i]:
% 31.19/31.41                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41                     ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ C @ D ) ) =
% 31.19/31.41                       ( k1_lattices @
% 31.19/31.41                         A @ ( k2_lattices @ A @ B @ C ) @ 
% 31.19/31.41                         ( k2_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 31.19/31.41  thf('19', plain,
% 31.19/31.41      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 31.19/31.41         (~ (v11_lattices @ X7)
% 31.19/31.41          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ((k2_lattices @ X7 @ X9 @ (k1_lattices @ X7 @ X8 @ X10))
% 31.19/31.41              = (k1_lattices @ X7 @ (k2_lattices @ X7 @ X9 @ X8) @ 
% 31.19/31.41                 (k2_lattices @ X7 @ X9 @ X10)))
% 31.19/31.41          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ~ (l3_lattices @ X7)
% 31.19/31.41          | (v2_struct_0 @ X7))),
% 31.19/31.41      inference('cnf', [status(esa)], [d11_lattices])).
% 31.19/31.41  thf('20', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (l3_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ 
% 31.19/31.41              (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B_3 @ sk_B_3) @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ 
% 31.19/31.41                  (k4_lattices @ sk_A @ sk_B_3 @ sk_B_3)) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1)))
% 31.19/31.41          | ~ (v11_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['18', '19'])).
% 31.19/31.41  thf('21', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('22', plain, ((v11_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('23', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ 
% 31.19/31.41              (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B_3 @ sk_B_3) @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ 
% 31.19/31.41                  (k4_lattices @ sk_A @ sk_B_3 @ sk_B_3)) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 31.19/31.41      inference('demod', [status(thm)], ['20', '21', '22'])).
% 31.19/31.41  thf('24', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('25', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(t21_lattices, axiom,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 31.19/31.41         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 31.19/31.41       ( ![B:$i]:
% 31.19/31.41         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41           ( ![C:$i]:
% 31.19/31.41             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41               ( ( r1_lattices @ A @ B @ C ) <=>
% 31.19/31.41                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 31.19/31.41  thf('26', plain,
% 31.19/31.41      (![X33 : $i, X34 : $i, X35 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 31.19/31.41          | ~ (r1_lattices @ X34 @ X33 @ X35)
% 31.19/31.41          | ((k2_lattices @ X34 @ X33 @ X35) = (X33))
% 31.19/31.41          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 31.19/31.41          | ~ (l3_lattices @ X34)
% 31.19/31.41          | ~ (v9_lattices @ X34)
% 31.19/31.41          | ~ (v8_lattices @ X34)
% 31.19/31.41          | (v2_struct_0 @ X34))),
% 31.19/31.41      inference('cnf', [status(esa)], [t21_lattices])).
% 31.19/31.41  thf('27', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v8_lattices @ sk_A)
% 31.19/31.41          | ~ (v9_lattices @ sk_A)
% 31.19/31.41          | ~ (l3_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_B_3 @ X0) = (sk_B_3))
% 31.19/31.41          | ~ (r1_lattices @ sk_A @ sk_B_3 @ X0))),
% 31.19/31.41      inference('sup-', [status(thm)], ['25', '26'])).
% 31.19/31.41  thf('28', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ X0)
% 31.19/31.41          | ~ (v10_lattices @ X0)
% 31.19/31.41          | (v8_lattices @ X0)
% 31.19/31.41          | ~ (l3_lattices @ X0))),
% 31.19/31.41      inference('cnf', [status(esa)], [cc1_lattices])).
% 31.19/31.41  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('30', plain,
% 31.19/31.41      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['28', '29'])).
% 31.19/31.41  thf('31', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('32', plain, ((v10_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('33', plain, ((v8_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.41  thf('34', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ X0)
% 31.19/31.41          | ~ (v10_lattices @ X0)
% 31.19/31.41          | (v9_lattices @ X0)
% 31.19/31.41          | ~ (l3_lattices @ X0))),
% 31.19/31.41      inference('cnf', [status(esa)], [cc1_lattices])).
% 31.19/31.41  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('36', plain,
% 31.19/31.41      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['34', '35'])).
% 31.19/31.41  thf('37', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('38', plain, ((v10_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('39', plain, ((v9_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 31.19/31.41  thf('40', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('41', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_B_3 @ X0) = (sk_B_3))
% 31.19/31.41          | ~ (r1_lattices @ sk_A @ sk_B_3 @ X0))),
% 31.19/31.41      inference('demod', [status(thm)], ['27', '33', '39', '40'])).
% 31.19/31.41  thf('42', plain,
% 31.19/31.41      ((~ (r1_lattices @ sk_A @ sk_B_3 @ sk_B_3)
% 31.19/31.41        | ((k2_lattices @ sk_A @ sk_B_3 @ sk_B_3) = (sk_B_3))
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['24', '41'])).
% 31.19/31.41  thf('43', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('44', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(d3_lattices, axiom,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 31.19/31.41       ( ![B:$i]:
% 31.19/31.41         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41           ( ![C:$i]:
% 31.19/31.41             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41               ( ( r1_lattices @ A @ B @ C ) <=>
% 31.19/31.41                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 31.19/31.41  thf('45', plain,
% 31.19/31.41      (![X11 : $i, X12 : $i, X13 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 31.19/31.41          | ((k1_lattices @ X12 @ X11 @ X13) != (X13))
% 31.19/31.41          | (r1_lattices @ X12 @ X11 @ X13)
% 31.19/31.41          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 31.19/31.41          | ~ (l2_lattices @ X12)
% 31.19/31.41          | (v2_struct_0 @ X12))),
% 31.19/31.41      inference('cnf', [status(esa)], [d3_lattices])).
% 31.19/31.41  thf('46', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (r1_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41          | ((k1_lattices @ sk_A @ sk_B_3 @ X0) != (X0)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['44', '45'])).
% 31.19/31.41  thf('47', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('48', plain,
% 31.19/31.41      (![X24 : $i]: ((l2_lattices @ X24) | ~ (l3_lattices @ X24))),
% 31.19/31.41      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 31.19/31.41  thf('49', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('50', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (r1_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41          | ((k1_lattices @ sk_A @ sk_B_3 @ X0) != (X0)))),
% 31.19/31.41      inference('demod', [status(thm)], ['46', '49'])).
% 31.19/31.41  thf('51', plain,
% 31.19/31.41      ((((k1_lattices @ sk_A @ sk_B_3 @ sk_B_3) != (sk_B_3))
% 31.19/31.41        | (r1_lattices @ sk_A @ sk_B_3 @ sk_B_3)
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['43', '50'])).
% 31.19/31.41  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('53', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_B_3 @ sk_B_3)
% 31.19/31.41        | ((k1_lattices @ sk_A @ sk_B_3 @ sk_B_3) != (sk_B_3)))),
% 31.19/31.41      inference('clc', [status(thm)], ['51', '52'])).
% 31.19/31.41  thf('54', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('55', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(redefinition_k3_lattices, axiom,
% 31.19/31.41    (![A:$i,B:$i,C:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 31.19/31.41         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 31.19/31.41         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 31.19/31.41       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 31.19/31.41  thf('56', plain,
% 31.19/31.41      (![X25 : $i, X26 : $i, X27 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ~ (l2_lattices @ X26)
% 31.19/31.41          | ~ (v4_lattices @ X26)
% 31.19/31.41          | (v2_struct_0 @ X26)
% 31.19/31.41          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ((k3_lattices @ X26 @ X25 @ X27) = (k1_lattices @ X26 @ X25 @ X27)))),
% 31.19/31.41      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 31.19/31.41  thf('57', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v4_lattices @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['55', '56'])).
% 31.19/31.41  thf('58', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ X0)
% 31.19/31.41          | ~ (v10_lattices @ X0)
% 31.19/31.41          | (v4_lattices @ X0)
% 31.19/31.41          | ~ (l3_lattices @ X0))),
% 31.19/31.41      inference('cnf', [status(esa)], [cc1_lattices])).
% 31.19/31.41  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('60', plain,
% 31.19/31.41      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['58', '59'])).
% 31.19/31.41  thf('61', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('62', plain, ((v10_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('63', plain, ((v4_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['60', '61', '62'])).
% 31.19/31.41  thf('64', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('65', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['57', '63', '64'])).
% 31.19/31.41  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('67', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_B_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['65', '66'])).
% 31.19/31.41  thf('68', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_B_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_B_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['54', '67'])).
% 31.19/31.41  thf('69', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_B_3 @ sk_B_3)
% 31.19/31.41        | ((k3_lattices @ sk_A @ sk_B_3 @ sk_B_3) != (sk_B_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['53', '68'])).
% 31.19/31.41  thf('70', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(t17_lattices, axiom,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 31.19/31.41         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 31.19/31.41       ( ![B:$i]:
% 31.19/31.41         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41           ( ( k1_lattices @ A @ B @ B ) = ( B ) ) ) ) ))).
% 31.19/31.41  thf('71', plain,
% 31.19/31.41      (![X31 : $i, X32 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 31.19/31.41          | ((k1_lattices @ X32 @ X31 @ X31) = (X31))
% 31.19/31.41          | ~ (l3_lattices @ X32)
% 31.19/31.41          | ~ (v9_lattices @ X32)
% 31.19/31.41          | ~ (v8_lattices @ X32)
% 31.19/31.41          | ~ (v6_lattices @ X32)
% 31.19/31.41          | (v2_struct_0 @ X32))),
% 31.19/31.41      inference('cnf', [status(esa)], [t17_lattices])).
% 31.19/31.41  thf('72', plain,
% 31.19/31.41      (((v2_struct_0 @ sk_A)
% 31.19/31.41        | ~ (v6_lattices @ sk_A)
% 31.19/31.41        | ~ (v8_lattices @ sk_A)
% 31.19/31.41        | ~ (v9_lattices @ sk_A)
% 31.19/31.41        | ~ (l3_lattices @ sk_A)
% 31.19/31.41        | ((k1_lattices @ sk_A @ sk_B_3 @ sk_B_3) = (sk_B_3)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['70', '71'])).
% 31.19/31.41  thf('73', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('74', plain, ((v8_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.41  thf('75', plain, ((v9_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 31.19/31.41  thf('76', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('77', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_B_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_B_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['54', '67'])).
% 31.19/31.41  thf('78', plain,
% 31.19/31.41      (((v2_struct_0 @ sk_A)
% 31.19/31.41        | ((k3_lattices @ sk_A @ sk_B_3 @ sk_B_3) = (sk_B_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['72', '73', '74', '75', '76', '77'])).
% 31.19/31.41  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('80', plain, (((k3_lattices @ sk_A @ sk_B_3 @ sk_B_3) = (sk_B_3))),
% 31.19/31.41      inference('clc', [status(thm)], ['78', '79'])).
% 31.19/31.41  thf('81', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_B_3 @ sk_B_3) | ((sk_B_3) != (sk_B_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['69', '80'])).
% 31.19/31.41  thf('82', plain, ((r1_lattices @ sk_A @ sk_B_3 @ sk_B_3)),
% 31.19/31.41      inference('simplify', [status(thm)], ['81'])).
% 31.19/31.41  thf('83', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('84', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(redefinition_k4_lattices, axiom,
% 31.19/31.41    (![A:$i,B:$i,C:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 31.19/31.41         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 31.19/31.41         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 31.19/31.41       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 31.19/31.41  thf('85', plain,
% 31.19/31.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 31.19/31.41          | ~ (l1_lattices @ X29)
% 31.19/31.41          | ~ (v6_lattices @ X29)
% 31.19/31.41          | (v2_struct_0 @ X29)
% 31.19/31.41          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 31.19/31.41          | ((k4_lattices @ X29 @ X28 @ X30) = (k2_lattices @ X29 @ X28 @ X30)))),
% 31.19/31.41      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 31.19/31.41  thf('86', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k2_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v6_lattices @ sk_A)
% 31.19/31.41          | ~ (l1_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['84', '85'])).
% 31.19/31.41  thf('87', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('88', plain, ((l1_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['12', '13'])).
% 31.19/31.41  thf('89', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k2_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['86', '87', '88'])).
% 31.19/31.41  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('91', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['89', '90'])).
% 31.19/31.41  thf('92', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_B_3 @ sk_B_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_B_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['83', '91'])).
% 31.19/31.41  thf('93', plain,
% 31.19/31.41      ((((k4_lattices @ sk_A @ sk_B_3 @ sk_B_3) = (sk_B_3))
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['42', '82', '92'])).
% 31.19/31.41  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('95', plain, (((k4_lattices @ sk_A @ sk_B_3 @ sk_B_3) = (sk_B_3))),
% 31.19/31.41      inference('clc', [status(thm)], ['93', '94'])).
% 31.19/31.41  thf('96', plain, (((k4_lattices @ sk_A @ sk_B_3 @ sk_B_3) = (sk_B_3))),
% 31.19/31.41      inference('clc', [status(thm)], ['93', '94'])).
% 31.19/31.41  thf('97', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_3 @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 31.19/31.41      inference('demod', [status(thm)], ['23', '95', '96'])).
% 31.19/31.41  thf('98', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41               (k2_lattices @ sk_A @ sk_C_3 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['1', '97'])).
% 31.19/31.41  thf('99', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('100', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('101', plain,
% 31.19/31.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 31.19/31.41          | ~ (l1_lattices @ X29)
% 31.19/31.41          | ~ (v6_lattices @ X29)
% 31.19/31.41          | (v2_struct_0 @ X29)
% 31.19/31.41          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 31.19/31.41          | ((k4_lattices @ X29 @ X28 @ X30) = (k2_lattices @ X29 @ X28 @ X30)))),
% 31.19/31.41      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 31.19/31.41  thf('102', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41            = (k2_lattices @ sk_A @ sk_C_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v6_lattices @ sk_A)
% 31.19/31.41          | ~ (l1_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['100', '101'])).
% 31.19/31.41  thf('103', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('104', plain, ((l1_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['12', '13'])).
% 31.19/31.41  thf('105', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41            = (k2_lattices @ sk_A @ sk_C_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['102', '103', '104'])).
% 31.19/31.41  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('107', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41              = (k2_lattices @ sk_A @ sk_C_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['105', '106'])).
% 31.19/31.41  thf('108', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['99', '107'])).
% 31.19/31.41  thf('109', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41               (k2_lattices @ sk_A @ sk_C_3 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['98', '108'])).
% 31.19/31.41  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('111', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ sk_C_3 @ X0))))),
% 31.19/31.41      inference('clc', [status(thm)], ['109', '110'])).
% 31.19/31.41  thf('112', plain,
% 31.19/31.41      (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_B_3 @ sk_D_2))
% 31.19/31.41         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41            (k2_lattices @ sk_A @ sk_C_3 @ sk_D_2)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['0', '111'])).
% 31.19/31.41  thf('113', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('114', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_B_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['65', '66'])).
% 31.19/31.41  thf('115', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_D_2)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.41      inference('sup-', [status(thm)], ['113', '114'])).
% 31.19/31.41  thf('116', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k3_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('117', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('118', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(commutativity_k3_lattices, axiom,
% 31.19/31.41    (![A:$i,B:$i,C:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 31.19/31.41         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 31.19/31.41         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 31.19/31.41       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 31.19/31.41  thf('119', plain,
% 31.19/31.41      (![X1 : $i, X2 : $i, X3 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 31.19/31.41          | ~ (l2_lattices @ X2)
% 31.19/31.41          | ~ (v4_lattices @ X2)
% 31.19/31.41          | (v2_struct_0 @ X2)
% 31.19/31.41          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 31.19/31.41          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 31.19/31.41      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 31.19/31.41  thf('120', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k3_lattices @ sk_A @ X0 @ sk_B_3))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v4_lattices @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['118', '119'])).
% 31.19/31.41  thf('121', plain, ((v4_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['60', '61', '62'])).
% 31.19/31.41  thf('122', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('123', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k3_lattices @ sk_A @ X0 @ sk_B_3))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['120', '121', '122'])).
% 31.19/31.41  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('125', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k3_lattices @ sk_A @ X0 @ sk_B_3)))),
% 31.19/31.41      inference('clc', [status(thm)], ['123', '124'])).
% 31.19/31.41  thf('126', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k3_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['117', '125'])).
% 31.19/31.41  thf('127', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k3_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.41      inference('demod', [status(thm)], ['116', '126'])).
% 31.19/31.41  thf('128', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.41      inference('demod', [status(thm)], ['115', '127'])).
% 31.19/31.41  thf('129', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('130', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('131', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('132', plain,
% 31.19/31.41      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 31.19/31.41         (~ (v11_lattices @ X7)
% 31.19/31.41          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ((k2_lattices @ X7 @ X9 @ (k1_lattices @ X7 @ X8 @ X10))
% 31.19/31.41              = (k1_lattices @ X7 @ (k2_lattices @ X7 @ X9 @ X8) @ 
% 31.19/31.41                 (k2_lattices @ X7 @ X9 @ X10)))
% 31.19/31.41          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ~ (l3_lattices @ X7)
% 31.19/31.41          | (v2_struct_0 @ X7))),
% 31.19/31.41      inference('cnf', [status(esa)], [d11_lattices])).
% 31.19/31.41  thf('133', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (l3_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_C_3 @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1)))
% 31.19/31.41          | ~ (v11_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['131', '132'])).
% 31.19/31.41  thf('134', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('135', plain, ((v11_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('136', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_C_3 @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 31.19/31.41      inference('demod', [status(thm)], ['133', '134', '135'])).
% 31.19/31.41  thf('137', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_C_3 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_C_3 @ sk_C_3) @ 
% 31.19/31.41               (k2_lattices @ sk_A @ sk_C_3 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['130', '136'])).
% 31.19/31.41  thf('138', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('139', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41              = (k2_lattices @ sk_A @ sk_C_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['105', '106'])).
% 31.19/31.41  thf('140', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_C_3 @ sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['138', '139'])).
% 31.19/31.41  thf('141', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('142', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('143', plain,
% 31.19/31.41      (![X33 : $i, X34 : $i, X35 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 31.19/31.41          | ~ (r1_lattices @ X34 @ X33 @ X35)
% 31.19/31.41          | ((k2_lattices @ X34 @ X33 @ X35) = (X33))
% 31.19/31.41          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 31.19/31.41          | ~ (l3_lattices @ X34)
% 31.19/31.41          | ~ (v9_lattices @ X34)
% 31.19/31.41          | ~ (v8_lattices @ X34)
% 31.19/31.41          | (v2_struct_0 @ X34))),
% 31.19/31.41      inference('cnf', [status(esa)], [t21_lattices])).
% 31.19/31.41  thf('144', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v8_lattices @ sk_A)
% 31.19/31.41          | ~ (v9_lattices @ sk_A)
% 31.19/31.41          | ~ (l3_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_C_3 @ X0) = (sk_C_3))
% 31.19/31.41          | ~ (r1_lattices @ sk_A @ sk_C_3 @ X0))),
% 31.19/31.41      inference('sup-', [status(thm)], ['142', '143'])).
% 31.19/31.41  thf('145', plain, ((v8_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.41  thf('146', plain, ((v9_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 31.19/31.41  thf('147', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('148', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_C_3 @ X0) = (sk_C_3))
% 31.19/31.41          | ~ (r1_lattices @ sk_A @ sk_C_3 @ X0))),
% 31.19/31.41      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 31.19/31.41  thf('149', plain,
% 31.19/31.41      ((~ (r1_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41        | ((k2_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3))
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['141', '148'])).
% 31.19/31.41  thf('150', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('151', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('152', plain,
% 31.19/31.41      (![X11 : $i, X12 : $i, X13 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 31.19/31.41          | ((k1_lattices @ X12 @ X11 @ X13) != (X13))
% 31.19/31.41          | (r1_lattices @ X12 @ X11 @ X13)
% 31.19/31.41          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 31.19/31.41          | ~ (l2_lattices @ X12)
% 31.19/31.41          | (v2_struct_0 @ X12))),
% 31.19/31.41      inference('cnf', [status(esa)], [d3_lattices])).
% 31.19/31.41  thf('153', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (r1_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41          | ((k1_lattices @ sk_A @ sk_C_3 @ X0) != (X0)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['151', '152'])).
% 31.19/31.41  thf('154', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('155', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (r1_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41          | ((k1_lattices @ sk_A @ sk_C_3 @ X0) != (X0)))),
% 31.19/31.41      inference('demod', [status(thm)], ['153', '154'])).
% 31.19/31.41  thf('156', plain,
% 31.19/31.41      ((((k1_lattices @ sk_A @ sk_C_3 @ sk_C_3) != (sk_C_3))
% 31.19/31.41        | (r1_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['150', '155'])).
% 31.19/31.41  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('158', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41        | ((k1_lattices @ sk_A @ sk_C_3 @ sk_C_3) != (sk_C_3)))),
% 31.19/31.41      inference('clc', [status(thm)], ['156', '157'])).
% 31.19/31.41  thf('159', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('160', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('161', plain,
% 31.19/31.41      (![X25 : $i, X26 : $i, X27 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ~ (l2_lattices @ X26)
% 31.19/31.41          | ~ (v4_lattices @ X26)
% 31.19/31.41          | (v2_struct_0 @ X26)
% 31.19/31.41          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ((k3_lattices @ X26 @ X25 @ X27) = (k1_lattices @ X26 @ X25 @ X27)))),
% 31.19/31.41      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 31.19/31.41  thf('162', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_C_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v4_lattices @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['160', '161'])).
% 31.19/31.41  thf('163', plain, ((v4_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['60', '61', '62'])).
% 31.19/31.41  thf('164', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('165', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_C_3 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['162', '163', '164'])).
% 31.19/31.41  thf('166', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('167', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_C_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['165', '166'])).
% 31.19/31.41  thf('168', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_C_3 @ sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['159', '167'])).
% 31.19/31.41  thf('169', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41        | ((k3_lattices @ sk_A @ sk_C_3 @ sk_C_3) != (sk_C_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['158', '168'])).
% 31.19/31.41  thf('170', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('171', plain,
% 31.19/31.41      (![X31 : $i, X32 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 31.19/31.41          | ((k1_lattices @ X32 @ X31 @ X31) = (X31))
% 31.19/31.41          | ~ (l3_lattices @ X32)
% 31.19/31.41          | ~ (v9_lattices @ X32)
% 31.19/31.41          | ~ (v8_lattices @ X32)
% 31.19/31.41          | ~ (v6_lattices @ X32)
% 31.19/31.41          | (v2_struct_0 @ X32))),
% 31.19/31.41      inference('cnf', [status(esa)], [t17_lattices])).
% 31.19/31.41  thf('172', plain,
% 31.19/31.41      (((v2_struct_0 @ sk_A)
% 31.19/31.41        | ~ (v6_lattices @ sk_A)
% 31.19/31.41        | ~ (v8_lattices @ sk_A)
% 31.19/31.41        | ~ (v9_lattices @ sk_A)
% 31.19/31.41        | ~ (l3_lattices @ sk_A)
% 31.19/31.41        | ((k1_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['170', '171'])).
% 31.19/31.41  thf('173', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('174', plain, ((v8_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.41  thf('175', plain, ((v9_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 31.19/31.41  thf('176', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('177', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_C_3 @ sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['159', '167'])).
% 31.19/31.41  thf('178', plain,
% 31.19/31.41      (((v2_struct_0 @ sk_A)
% 31.19/31.41        | ((k3_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3)))),
% 31.19/31.41      inference('demod', [status(thm)],
% 31.19/31.41                ['172', '173', '174', '175', '176', '177'])).
% 31.19/31.41  thf('179', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('180', plain, (((k3_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3))),
% 31.19/31.41      inference('clc', [status(thm)], ['178', '179'])).
% 31.19/31.41  thf('181', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_C_3 @ sk_C_3) | ((sk_C_3) != (sk_C_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['169', '180'])).
% 31.19/31.41  thf('182', plain, ((r1_lattices @ sk_A @ sk_C_3 @ sk_C_3)),
% 31.19/31.41      inference('simplify', [status(thm)], ['181'])).
% 31.19/31.41  thf('183', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_C_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_C_3 @ sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['138', '139'])).
% 31.19/31.41  thf('184', plain,
% 31.19/31.41      ((((k4_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3))
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['149', '182', '183'])).
% 31.19/31.41  thf('185', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('186', plain, (((k4_lattices @ sk_A @ sk_C_3 @ sk_C_3) = (sk_C_3))),
% 31.19/31.41      inference('clc', [status(thm)], ['184', '185'])).
% 31.19/31.41  thf('187', plain, (((sk_C_3) = (k2_lattices @ sk_A @ sk_C_3 @ sk_C_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['140', '186'])).
% 31.19/31.41  thf('188', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_C_3 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_C_3 @ (k2_lattices @ sk_A @ sk_C_3 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['137', '187'])).
% 31.19/31.41  thf('189', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('190', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_C_3 @ X0))
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_C_3 @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ sk_C_3 @ X0))))),
% 31.19/31.41      inference('clc', [status(thm)], ['188', '189'])).
% 31.19/31.41  thf('191', plain,
% 31.19/31.41      (((k2_lattices @ sk_A @ sk_C_3 @ (k1_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_C_3 @ 
% 31.19/31.41            (k2_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['129', '190'])).
% 31.19/31.41  thf('192', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('193', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_C_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['165', '166'])).
% 31.19/31.41  thf('194', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['192', '193'])).
% 31.19/31.41  thf('195', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['99', '107'])).
% 31.19/31.41  thf('196', plain,
% 31.19/31.41      (((k2_lattices @ sk_A @ sk_C_3 @ (k3_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_C_3 @ 
% 31.19/31.41            (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['191', '194', '195'])).
% 31.19/31.41  thf('197', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('198', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_3 @ X0) @ 
% 31.19/31.41             (u1_struct_0 @ sk_A)))),
% 31.19/31.41      inference('clc', [status(thm)], ['15', '16'])).
% 31.19/31.41  thf('199', plain,
% 31.19/31.41      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_B_3 @ sk_C_3) @ 
% 31.19/31.41        (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['197', '198'])).
% 31.19/31.41  thf('200', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('201', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(commutativity_k4_lattices, axiom,
% 31.19/31.41    (![A:$i,B:$i,C:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 31.19/31.41         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 31.19/31.41         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 31.19/31.41       ( ( k4_lattices @ A @ B @ C ) = ( k4_lattices @ A @ C @ B ) ) ))).
% 31.19/31.41  thf('202', plain,
% 31.19/31.41      (![X4 : $i, X5 : $i, X6 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 31.19/31.41          | ~ (l1_lattices @ X5)
% 31.19/31.41          | ~ (v6_lattices @ X5)
% 31.19/31.41          | (v2_struct_0 @ X5)
% 31.19/31.41          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 31.19/31.41          | ((k4_lattices @ X5 @ X4 @ X6) = (k4_lattices @ X5 @ X6 @ X4)))),
% 31.19/31.41      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 31.19/31.41  thf('203', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k4_lattices @ sk_A @ X0 @ sk_B_3))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v6_lattices @ sk_A)
% 31.19/31.41          | ~ (l1_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['201', '202'])).
% 31.19/31.41  thf('204', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('205', plain, ((l1_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['12', '13'])).
% 31.19/31.41  thf('206', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41            = (k4_lattices @ sk_A @ X0 @ sk_B_3))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['203', '204', '205'])).
% 31.19/31.41  thf('207', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('208', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k4_lattices @ sk_A @ X0 @ sk_B_3)))),
% 31.19/31.41      inference('clc', [status(thm)], ['206', '207'])).
% 31.19/31.41  thf('209', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['200', '208'])).
% 31.19/31.41  thf('210', plain,
% 31.19/31.41      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41        (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['199', '209'])).
% 31.19/31.41  thf('211', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_C_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['165', '166'])).
% 31.19/31.41  thf('212', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_C_3 @ 
% 31.19/31.41            (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['210', '211'])).
% 31.19/31.41  thf('213', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('214', plain,
% 31.19/31.41      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41        (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['199', '209'])).
% 31.19/31.41  thf('215', plain,
% 31.19/31.41      (![X25 : $i, X26 : $i, X27 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ~ (l2_lattices @ X26)
% 31.19/31.41          | ~ (v4_lattices @ X26)
% 31.19/31.41          | (v2_struct_0 @ X26)
% 31.19/31.41          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ((k3_lattices @ X26 @ X25 @ X27) = (k1_lattices @ X26 @ X25 @ X27)))),
% 31.19/31.41      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 31.19/31.41  thf('216', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v4_lattices @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['214', '215'])).
% 31.19/31.41  thf('217', plain, ((v4_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['60', '61', '62'])).
% 31.19/31.41  thf('218', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('219', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['216', '217', '218'])).
% 31.19/31.41  thf('220', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('221', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41                 X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['219', '220'])).
% 31.19/31.41  thf('222', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ sk_C_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41            sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['213', '221'])).
% 31.19/31.41  thf('223', plain,
% 31.19/31.41      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41        (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['199', '209'])).
% 31.19/31.41  thf('224', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('225', plain,
% 31.19/31.41      (![X1 : $i, X2 : $i, X3 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 31.19/31.41          | ~ (l2_lattices @ X2)
% 31.19/31.41          | ~ (v4_lattices @ X2)
% 31.19/31.41          | (v2_struct_0 @ X2)
% 31.19/31.41          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 31.19/31.41          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 31.19/31.41      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 31.19/31.41  thf('226', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41            = (k3_lattices @ sk_A @ X0 @ sk_C_3))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v4_lattices @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['224', '225'])).
% 31.19/31.41  thf('227', plain, ((v4_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['60', '61', '62'])).
% 31.19/31.41  thf('228', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('229', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41            = (k3_lattices @ sk_A @ X0 @ sk_C_3))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['226', '227', '228'])).
% 31.19/31.41  thf('230', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('231', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41              = (k3_lattices @ sk_A @ X0 @ sk_C_3)))),
% 31.19/31.41      inference('clc', [status(thm)], ['229', '230'])).
% 31.19/31.41  thf('232', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41            sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['223', '231'])).
% 31.19/31.41  thf('233', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41            sk_C_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['222', '232'])).
% 31.19/31.41  thf('234', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('235', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf(d8_lattices, axiom,
% 31.19/31.41    (![A:$i]:
% 31.19/31.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 31.19/31.41       ( ( v8_lattices @ A ) <=>
% 31.19/31.41         ( ![B:$i]:
% 31.19/31.41           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41             ( ![C:$i]:
% 31.19/31.41               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 31.19/31.41                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 31.19/31.41                   ( C ) ) ) ) ) ) ) ))).
% 31.19/31.41  thf('236', plain,
% 31.19/31.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 31.19/31.41         (~ (v8_lattices @ X18)
% 31.19/31.41          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 31.19/31.41          | ((k1_lattices @ X18 @ (k2_lattices @ X18 @ X20 @ X19) @ X19)
% 31.19/31.41              = (X19))
% 31.19/31.41          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 31.19/31.41          | ~ (l3_lattices @ X18)
% 31.19/31.41          | (v2_struct_0 @ X18))),
% 31.19/31.41      inference('cnf', [status(esa)], [d8_lattices])).
% 31.19/31.41  thf('237', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (l3_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ sk_C_3)
% 31.19/31.41              = (sk_C_3))
% 31.19/31.41          | ~ (v8_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['235', '236'])).
% 31.19/31.41  thf('238', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('239', plain, ((v8_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.41  thf('240', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ sk_C_3)
% 31.19/31.41              = (sk_C_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['237', '238', '239'])).
% 31.19/31.41  thf('241', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('242', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_3) @ sk_C_3)
% 31.19/31.41            = (sk_C_3))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 31.19/31.41      inference('clc', [status(thm)], ['240', '241'])).
% 31.19/31.41  thf('243', plain,
% 31.19/31.41      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_C_3) @ sk_C_3)
% 31.19/31.41         = (sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['234', '242'])).
% 31.19/31.41  thf('244', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('245', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['89', '90'])).
% 31.19/31.41  thf('246', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['244', '245'])).
% 31.19/31.41  thf('247', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['200', '208'])).
% 31.19/31.41  thf('248', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['246', '247'])).
% 31.19/31.41  thf('249', plain,
% 31.19/31.41      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ sk_C_3)
% 31.19/31.41         = (sk_C_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['243', '248'])).
% 31.19/31.41  thf('250', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (sk_C_3))),
% 31.19/31.41      inference('sup+', [status(thm)], ['233', '249'])).
% 31.19/31.41  thf('251', plain,
% 31.19/31.41      (((sk_C_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_C_3 @ 
% 31.19/31.41            (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['212', '250'])).
% 31.19/31.41  thf('252', plain,
% 31.19/31.41      (((sk_C_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_C_3 @ 
% 31.19/31.41            (k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.41      inference('sup+', [status(thm)], ['196', '251'])).
% 31.19/31.41  thf('253', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('254', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.41              = (k2_lattices @ sk_A @ sk_C_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['105', '106'])).
% 31.19/31.41  thf('255', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_D_2)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_C_3 @ sk_D_2))),
% 31.19/31.41      inference('sup-', [status(thm)], ['253', '254'])).
% 31.19/31.41  thf('256', plain,
% 31.19/31.41      (((sk_C_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41            (k4_lattices @ sk_A @ sk_C_3 @ sk_D_2)))),
% 31.19/31.41      inference('demod', [status(thm)], ['112', '128', '252', '255'])).
% 31.19/31.41  thf('257', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('258', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('259', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_B_3 @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_B_3) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 31.19/31.41      inference('demod', [status(thm)], ['23', '95', '96'])).
% 31.19/31.41  thf('260', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_D_2 @ sk_B_3) @ 
% 31.19/31.41               (k2_lattices @ sk_A @ sk_D_2 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['258', '259'])).
% 31.19/31.41  thf('261', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('262', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('263', plain,
% 31.19/31.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 31.19/31.41          | ~ (l1_lattices @ X29)
% 31.19/31.41          | ~ (v6_lattices @ X29)
% 31.19/31.41          | (v2_struct_0 @ X29)
% 31.19/31.41          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 31.19/31.41          | ((k4_lattices @ X29 @ X28 @ X30) = (k2_lattices @ X29 @ X28 @ X30)))),
% 31.19/31.41      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 31.19/31.41  thf('264', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41            = (k2_lattices @ sk_A @ sk_D_2 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v6_lattices @ sk_A)
% 31.19/31.41          | ~ (l1_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['262', '263'])).
% 31.19/31.41  thf('265', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('266', plain, ((l1_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['12', '13'])).
% 31.19/31.41  thf('267', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k4_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41            = (k2_lattices @ sk_A @ sk_D_2 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['264', '265', '266'])).
% 31.19/31.41  thf('268', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('269', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41              = (k2_lattices @ sk_A @ sk_D_2 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['267', '268'])).
% 31.19/31.41  thf('270', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_D_2 @ sk_B_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['261', '269'])).
% 31.19/31.41  thf('271', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k4_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('272', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['200', '208'])).
% 31.19/31.41  thf('273', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k4_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.41      inference('demod', [status(thm)], ['271', '272'])).
% 31.19/31.41  thf('274', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('275', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k4_lattices @ sk_A @ X0 @ sk_B_3)))),
% 31.19/31.41      inference('clc', [status(thm)], ['206', '207'])).
% 31.19/31.41  thf('276', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_B_3 @ sk_D_2)
% 31.19/31.41         = (k4_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['274', '275'])).
% 31.19/31.41  thf('277', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k4_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('sup+', [status(thm)], ['273', '276'])).
% 31.19/31.41  thf('278', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['270', '277'])).
% 31.19/31.41  thf('279', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41               (k2_lattices @ sk_A @ sk_D_2 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['260', '278'])).
% 31.19/31.41  thf('280', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('281', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_B_3 @ X0))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ sk_D_2 @ X0))))),
% 31.19/31.41      inference('clc', [status(thm)], ['279', '280'])).
% 31.19/31.41  thf('282', plain,
% 31.19/31.41      (((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41            (k2_lattices @ sk_A @ sk_D_2 @ sk_C_3)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['257', '281'])).
% 31.19/31.41  thf('283', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('284', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_B_3 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['65', '66'])).
% 31.19/31.41  thf('285', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['283', '284'])).
% 31.19/31.41  thf('286', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_C_3)
% 31.19/31.41         = (k3_lattices @ sk_A @ sk_C_3 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['117', '125'])).
% 31.19/31.41  thf('287', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_B_3 @ sk_C_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['285', '286'])).
% 31.19/31.41  thf('288', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('289', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('290', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('291', plain,
% 31.19/31.41      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 31.19/31.41         (~ (v11_lattices @ X7)
% 31.19/31.41          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ((k2_lattices @ X7 @ X9 @ (k1_lattices @ X7 @ X8 @ X10))
% 31.19/31.41              = (k1_lattices @ X7 @ (k2_lattices @ X7 @ X9 @ X8) @ 
% 31.19/31.41                 (k2_lattices @ X7 @ X9 @ X10)))
% 31.19/31.41          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 31.19/31.41          | ~ (l3_lattices @ X7)
% 31.19/31.41          | (v2_struct_0 @ X7))),
% 31.19/31.41      inference('cnf', [status(esa)], [d11_lattices])).
% 31.19/31.41  thf('292', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (l3_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_D_2 @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_2) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1)))
% 31.19/31.41          | ~ (v11_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['290', '291'])).
% 31.19/31.41  thf('293', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('294', plain, ((v11_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('295', plain,
% 31.19/31.41      (![X0 : $i, X1 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ sk_D_2 @ X1))
% 31.19/31.41              = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_2) @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ X0 @ X1))))),
% 31.19/31.41      inference('demod', [status(thm)], ['292', '293', '294'])).
% 31.19/31.41  thf('296', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_D_2 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_D_2 @ sk_D_2) @ 
% 31.19/31.41               (k2_lattices @ sk_A @ sk_D_2 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['289', '295'])).
% 31.19/31.41  thf('297', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('298', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k4_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41              = (k2_lattices @ sk_A @ sk_D_2 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['267', '268'])).
% 31.19/31.41  thf('299', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_D_2 @ sk_D_2)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_D_2 @ sk_D_2))),
% 31.19/31.41      inference('sup-', [status(thm)], ['297', '298'])).
% 31.19/31.41  thf('300', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('301', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('302', plain,
% 31.19/31.41      (![X33 : $i, X34 : $i, X35 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 31.19/31.41          | ~ (r1_lattices @ X34 @ X33 @ X35)
% 31.19/31.41          | ((k2_lattices @ X34 @ X33 @ X35) = (X33))
% 31.19/31.41          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 31.19/31.41          | ~ (l3_lattices @ X34)
% 31.19/31.41          | ~ (v9_lattices @ X34)
% 31.19/31.41          | ~ (v8_lattices @ X34)
% 31.19/31.41          | (v2_struct_0 @ X34))),
% 31.19/31.41      inference('cnf', [status(esa)], [t21_lattices])).
% 31.19/31.41  thf('303', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v8_lattices @ sk_A)
% 31.19/31.41          | ~ (v9_lattices @ sk_A)
% 31.19/31.41          | ~ (l3_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_D_2 @ X0) = (sk_D_2))
% 31.19/31.41          | ~ (r1_lattices @ sk_A @ sk_D_2 @ X0))),
% 31.19/31.41      inference('sup-', [status(thm)], ['301', '302'])).
% 31.19/31.41  thf('304', plain, ((v8_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.41  thf('305', plain, ((v9_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 31.19/31.41  thf('306', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('307', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_D_2 @ X0) = (sk_D_2))
% 31.19/31.41          | ~ (r1_lattices @ sk_A @ sk_D_2 @ X0))),
% 31.19/31.41      inference('demod', [status(thm)], ['303', '304', '305', '306'])).
% 31.19/31.41  thf('308', plain,
% 31.19/31.41      ((~ (r1_lattices @ sk_A @ sk_D_2 @ sk_D_2)
% 31.19/31.41        | ((k2_lattices @ sk_A @ sk_D_2 @ sk_D_2) = (sk_D_2))
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['300', '307'])).
% 31.19/31.41  thf('309', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('310', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('311', plain,
% 31.19/31.41      (![X11 : $i, X12 : $i, X13 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 31.19/31.41          | ((k1_lattices @ X12 @ X11 @ X13) != (X13))
% 31.19/31.41          | (r1_lattices @ X12 @ X11 @ X13)
% 31.19/31.41          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 31.19/31.41          | ~ (l2_lattices @ X12)
% 31.19/31.41          | (v2_struct_0 @ X12))),
% 31.19/31.41      inference('cnf', [status(esa)], [d3_lattices])).
% 31.19/31.41  thf('312', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (r1_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41          | ((k1_lattices @ sk_A @ sk_D_2 @ X0) != (X0)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['310', '311'])).
% 31.19/31.41  thf('313', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('314', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         ((v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (r1_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41          | ((k1_lattices @ sk_A @ sk_D_2 @ X0) != (X0)))),
% 31.19/31.41      inference('demod', [status(thm)], ['312', '313'])).
% 31.19/31.41  thf('315', plain,
% 31.19/31.41      ((((k1_lattices @ sk_A @ sk_D_2 @ sk_D_2) != (sk_D_2))
% 31.19/31.41        | (r1_lattices @ sk_A @ sk_D_2 @ sk_D_2)
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['309', '314'])).
% 31.19/31.41  thf('316', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('317', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_D_2 @ sk_D_2)
% 31.19/31.41        | ((k1_lattices @ sk_A @ sk_D_2 @ sk_D_2) != (sk_D_2)))),
% 31.19/31.41      inference('clc', [status(thm)], ['315', '316'])).
% 31.19/31.41  thf('318', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('319', plain,
% 31.19/31.41      (![X31 : $i, X32 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 31.19/31.41          | ((k1_lattices @ X32 @ X31 @ X31) = (X31))
% 31.19/31.41          | ~ (l3_lattices @ X32)
% 31.19/31.41          | ~ (v9_lattices @ X32)
% 31.19/31.41          | ~ (v8_lattices @ X32)
% 31.19/31.41          | ~ (v6_lattices @ X32)
% 31.19/31.41          | (v2_struct_0 @ X32))),
% 31.19/31.41      inference('cnf', [status(esa)], [t17_lattices])).
% 31.19/31.41  thf('320', plain,
% 31.19/31.41      (((v2_struct_0 @ sk_A)
% 31.19/31.41        | ~ (v6_lattices @ sk_A)
% 31.19/31.41        | ~ (v8_lattices @ sk_A)
% 31.19/31.41        | ~ (v9_lattices @ sk_A)
% 31.19/31.41        | ~ (l3_lattices @ sk_A)
% 31.19/31.41        | ((k1_lattices @ sk_A @ sk_D_2 @ sk_D_2) = (sk_D_2)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['318', '319'])).
% 31.19/31.41  thf('321', plain, ((v6_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.41  thf('322', plain, ((v8_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.41  thf('323', plain, ((v9_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['36', '37', '38'])).
% 31.19/31.41  thf('324', plain, ((l3_lattices @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('325', plain,
% 31.19/31.41      (((v2_struct_0 @ sk_A)
% 31.19/31.41        | ((k1_lattices @ sk_A @ sk_D_2 @ sk_D_2) = (sk_D_2)))),
% 31.19/31.41      inference('demod', [status(thm)], ['320', '321', '322', '323', '324'])).
% 31.19/31.41  thf('326', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('327', plain, (((k1_lattices @ sk_A @ sk_D_2 @ sk_D_2) = (sk_D_2))),
% 31.19/31.41      inference('clc', [status(thm)], ['325', '326'])).
% 31.19/31.41  thf('328', plain,
% 31.19/31.41      (((r1_lattices @ sk_A @ sk_D_2 @ sk_D_2) | ((sk_D_2) != (sk_D_2)))),
% 31.19/31.41      inference('demod', [status(thm)], ['317', '327'])).
% 31.19/31.41  thf('329', plain, ((r1_lattices @ sk_A @ sk_D_2 @ sk_D_2)),
% 31.19/31.41      inference('simplify', [status(thm)], ['328'])).
% 31.19/31.41  thf('330', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_D_2 @ sk_D_2)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_D_2 @ sk_D_2))),
% 31.19/31.41      inference('sup-', [status(thm)], ['297', '298'])).
% 31.19/31.41  thf('331', plain,
% 31.19/31.41      ((((k4_lattices @ sk_A @ sk_D_2 @ sk_D_2) = (sk_D_2))
% 31.19/31.41        | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['308', '329', '330'])).
% 31.19/31.41  thf('332', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('333', plain, (((k4_lattices @ sk_A @ sk_D_2 @ sk_D_2) = (sk_D_2))),
% 31.19/31.41      inference('clc', [status(thm)], ['331', '332'])).
% 31.19/31.41  thf('334', plain, (((sk_D_2) = (k2_lattices @ sk_A @ sk_D_2 @ sk_D_2))),
% 31.19/31.41      inference('demod', [status(thm)], ['299', '333'])).
% 31.19/31.41  thf('335', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_D_2 @ X0))
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_D_2 @ (k2_lattices @ sk_A @ sk_D_2 @ X0)))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['296', '334'])).
% 31.19/31.41  thf('336', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('337', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_D_2 @ X0))
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_D_2 @ 
% 31.19/31.41                 (k2_lattices @ sk_A @ sk_D_2 @ X0))))),
% 31.19/31.41      inference('clc', [status(thm)], ['335', '336'])).
% 31.19/31.41  thf('338', plain,
% 31.19/31.41      (((k2_lattices @ sk_A @ sk_D_2 @ (k1_lattices @ sk_A @ sk_D_2 @ sk_B_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_D_2 @ 
% 31.19/31.41            (k2_lattices @ sk_A @ sk_D_2 @ sk_B_3)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['288', '337'])).
% 31.19/31.41  thf('339', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('340', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('341', plain,
% 31.19/31.41      (![X25 : $i, X26 : $i, X27 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ~ (l2_lattices @ X26)
% 31.19/31.41          | ~ (v4_lattices @ X26)
% 31.19/31.41          | (v2_struct_0 @ X26)
% 31.19/31.41          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 31.19/31.41          | ((k3_lattices @ X26 @ X25 @ X27) = (k1_lattices @ X26 @ X25 @ X27)))),
% 31.19/31.41      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 31.19/31.41  thf('342', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_D_2 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v4_lattices @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['340', '341'])).
% 31.19/31.41  thf('343', plain, ((v4_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['60', '61', '62'])).
% 31.19/31.41  thf('344', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('345', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41            = (k1_lattices @ sk_A @ sk_D_2 @ X0))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['342', '343', '344'])).
% 31.19/31.41  thf('346', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('347', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_D_2 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['345', '346'])).
% 31.19/31.41  thf('348', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_D_2 @ sk_B_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['339', '347'])).
% 31.19/31.41  thf('349', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k3_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.41      inference('demod', [status(thm)], ['116', '126'])).
% 31.19/31.41  thf('350', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('351', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.41              = (k3_lattices @ sk_A @ X0 @ sk_B_3)))),
% 31.19/31.41      inference('clc', [status(thm)], ['123', '124'])).
% 31.19/31.41  thf('352', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_B_3 @ sk_D_2)
% 31.19/31.41         = (k3_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('sup-', [status(thm)], ['350', '351'])).
% 31.19/31.41  thf('353', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k3_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('sup+', [status(thm)], ['349', '352'])).
% 31.19/31.41  thf('354', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['348', '353'])).
% 31.19/31.41  thf('355', plain,
% 31.19/31.41      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.41         = (k2_lattices @ sk_A @ sk_D_2 @ sk_B_3))),
% 31.19/31.41      inference('demod', [status(thm)], ['270', '277'])).
% 31.19/31.41  thf('356', plain,
% 31.19/31.41      (((k2_lattices @ sk_A @ sk_D_2 @ (k3_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_D_2 @ 
% 31.19/31.41            (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.41      inference('demod', [status(thm)], ['338', '354', '355'])).
% 31.19/31.41  thf('357', plain,
% 31.19/31.41      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41        (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['199', '209'])).
% 31.19/31.41  thf('358', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ sk_D_2 @ X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['345', '346'])).
% 31.19/31.41  thf('359', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ sk_D_2 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.41         = (k1_lattices @ sk_A @ sk_D_2 @ 
% 31.19/31.41            (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.41      inference('sup-', [status(thm)], ['357', '358'])).
% 31.19/31.41  thf('360', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('361', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | ((k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ X0)
% 31.19/31.41              = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41                 X0)))),
% 31.19/31.41      inference('clc', [status(thm)], ['219', '220'])).
% 31.19/31.41  thf('362', plain,
% 31.19/31.41      (((k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ sk_D_2)
% 31.19/31.41         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41            sk_D_2))),
% 31.19/31.41      inference('sup-', [status(thm)], ['360', '361'])).
% 31.19/31.41  thf('363', plain,
% 31.19/31.41      ((m1_subset_1 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.41        (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('demod', [status(thm)], ['199', '209'])).
% 31.19/31.41  thf('364', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.41  thf('365', plain,
% 31.19/31.41      (![X1 : $i, X2 : $i, X3 : $i]:
% 31.19/31.41         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 31.19/31.41          | ~ (l2_lattices @ X2)
% 31.19/31.41          | ~ (v4_lattices @ X2)
% 31.19/31.41          | (v2_struct_0 @ X2)
% 31.19/31.41          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 31.19/31.41          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 31.19/31.41      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 31.19/31.41  thf('366', plain,
% 31.19/31.41      (![X0 : $i]:
% 31.19/31.41         (((k3_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.41            = (k3_lattices @ sk_A @ X0 @ sk_D_2))
% 31.19/31.41          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.41          | (v2_struct_0 @ sk_A)
% 31.19/31.41          | ~ (v4_lattices @ sk_A)
% 31.19/31.41          | ~ (l2_lattices @ sk_A))),
% 31.19/31.41      inference('sup-', [status(thm)], ['364', '365'])).
% 31.19/31.41  thf('367', plain, ((v4_lattices @ sk_A)),
% 31.19/31.41      inference('demod', [status(thm)], ['60', '61', '62'])).
% 31.19/31.41  thf('368', plain, ((l2_lattices @ sk_A)),
% 31.19/31.41      inference('sup-', [status(thm)], ['47', '48'])).
% 31.19/31.41  thf('369', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (((k3_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.42            = (k3_lattices @ sk_A @ X0 @ sk_D_2))
% 31.19/31.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | (v2_struct_0 @ sk_A))),
% 31.19/31.42      inference('demod', [status(thm)], ['366', '367', '368'])).
% 31.19/31.42  thf('370', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('371', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | ((k3_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.42              = (k3_lattices @ sk_A @ X0 @ sk_D_2)))),
% 31.19/31.42      inference('clc', [status(thm)], ['369', '370'])).
% 31.19/31.42  thf('372', plain,
% 31.19/31.42      (((k3_lattices @ sk_A @ sk_D_2 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.42         = (k3_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.42            sk_D_2))),
% 31.19/31.42      inference('sup-', [status(thm)], ['363', '371'])).
% 31.19/31.42  thf('373', plain,
% 31.19/31.42      (((k3_lattices @ sk_A @ sk_D_2 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.42         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.42            sk_D_2))),
% 31.19/31.42      inference('demod', [status(thm)], ['362', '372'])).
% 31.19/31.42  thf('374', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('375', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('376', plain,
% 31.19/31.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 31.19/31.42         (~ (v8_lattices @ X18)
% 31.19/31.42          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 31.19/31.42          | ((k1_lattices @ X18 @ (k2_lattices @ X18 @ X20 @ X19) @ X19)
% 31.19/31.42              = (X19))
% 31.19/31.42          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 31.19/31.42          | ~ (l3_lattices @ X18)
% 31.19/31.42          | (v2_struct_0 @ X18))),
% 31.19/31.42      inference('cnf', [status(esa)], [d8_lattices])).
% 31.19/31.42  thf('377', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         ((v2_struct_0 @ sk_A)
% 31.19/31.42          | ~ (l3_lattices @ sk_A)
% 31.19/31.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_2) @ sk_D_2)
% 31.19/31.42              = (sk_D_2))
% 31.19/31.42          | ~ (v8_lattices @ sk_A))),
% 31.19/31.42      inference('sup-', [status(thm)], ['375', '376'])).
% 31.19/31.42  thf('378', plain, ((l3_lattices @ sk_A)),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('379', plain, ((v8_lattices @ sk_A)),
% 31.19/31.42      inference('demod', [status(thm)], ['30', '31', '32'])).
% 31.19/31.42  thf('380', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         ((v2_struct_0 @ sk_A)
% 31.19/31.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | ((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_2) @ sk_D_2)
% 31.19/31.42              = (sk_D_2)))),
% 31.19/31.42      inference('demod', [status(thm)], ['377', '378', '379'])).
% 31.19/31.42  thf('381', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('382', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_D_2) @ sk_D_2)
% 31.19/31.42            = (sk_D_2))
% 31.19/31.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 31.19/31.42      inference('clc', [status(thm)], ['380', '381'])).
% 31.19/31.42  thf('383', plain,
% 31.19/31.42      (((k1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_3 @ sk_D_2) @ sk_D_2)
% 31.19/31.42         = (sk_D_2))),
% 31.19/31.42      inference('sup-', [status(thm)], ['374', '382'])).
% 31.19/31.42  thf('384', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('385', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | ((k4_lattices @ sk_A @ sk_B_3 @ X0)
% 31.19/31.42              = (k2_lattices @ sk_A @ sk_B_3 @ X0)))),
% 31.19/31.42      inference('clc', [status(thm)], ['89', '90'])).
% 31.19/31.42  thf('386', plain,
% 31.19/31.42      (((k4_lattices @ sk_A @ sk_B_3 @ sk_D_2)
% 31.19/31.42         = (k2_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.42      inference('sup-', [status(thm)], ['384', '385'])).
% 31.19/31.42  thf('387', plain,
% 31.19/31.42      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.42         = (k4_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.42      inference('demod', [status(thm)], ['271', '272'])).
% 31.19/31.42  thf('388', plain,
% 31.19/31.42      (((k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)
% 31.19/31.42         = (k2_lattices @ sk_A @ sk_B_3 @ sk_D_2))),
% 31.19/31.42      inference('demod', [status(thm)], ['386', '387'])).
% 31.19/31.42  thf('389', plain,
% 31.19/31.42      (((k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ sk_D_2)
% 31.19/31.42         = (sk_D_2))),
% 31.19/31.42      inference('demod', [status(thm)], ['383', '388'])).
% 31.19/31.42  thf('390', plain,
% 31.19/31.42      (((k3_lattices @ sk_A @ sk_D_2 @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3))
% 31.19/31.42         = (sk_D_2))),
% 31.19/31.42      inference('sup+', [status(thm)], ['373', '389'])).
% 31.19/31.42  thf('391', plain,
% 31.19/31.42      (((sk_D_2)
% 31.19/31.42         = (k1_lattices @ sk_A @ sk_D_2 @ 
% 31.19/31.42            (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.42      inference('demod', [status(thm)], ['359', '390'])).
% 31.19/31.42  thf('392', plain,
% 31.19/31.42      (((sk_D_2)
% 31.19/31.42         = (k2_lattices @ sk_A @ sk_D_2 @ 
% 31.19/31.42            (k3_lattices @ sk_A @ sk_C_3 @ sk_B_3)))),
% 31.19/31.42      inference('sup+', [status(thm)], ['356', '391'])).
% 31.19/31.42  thf('393', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('394', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | ((k4_lattices @ sk_A @ sk_D_2 @ X0)
% 31.19/31.42              = (k2_lattices @ sk_A @ sk_D_2 @ X0)))),
% 31.19/31.42      inference('clc', [status(thm)], ['267', '268'])).
% 31.19/31.42  thf('395', plain,
% 31.19/31.42      (((k4_lattices @ sk_A @ sk_D_2 @ sk_C_3)
% 31.19/31.42         = (k2_lattices @ sk_A @ sk_D_2 @ sk_C_3))),
% 31.19/31.42      inference('sup-', [status(thm)], ['393', '394'])).
% 31.19/31.42  thf('396', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('397', plain, ((m1_subset_1 @ sk_C_3 @ (u1_struct_0 @ sk_A))),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('398', plain,
% 31.19/31.42      (![X4 : $i, X5 : $i, X6 : $i]:
% 31.19/31.42         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 31.19/31.42          | ~ (l1_lattices @ X5)
% 31.19/31.42          | ~ (v6_lattices @ X5)
% 31.19/31.42          | (v2_struct_0 @ X5)
% 31.19/31.42          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 31.19/31.42          | ((k4_lattices @ X5 @ X4 @ X6) = (k4_lattices @ X5 @ X6 @ X4)))),
% 31.19/31.42      inference('cnf', [status(esa)], [commutativity_k4_lattices])).
% 31.19/31.42  thf('399', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.42            = (k4_lattices @ sk_A @ X0 @ sk_C_3))
% 31.19/31.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | (v2_struct_0 @ sk_A)
% 31.19/31.42          | ~ (v6_lattices @ sk_A)
% 31.19/31.42          | ~ (l1_lattices @ sk_A))),
% 31.19/31.42      inference('sup-', [status(thm)], ['397', '398'])).
% 31.19/31.42  thf('400', plain, ((v6_lattices @ sk_A)),
% 31.19/31.42      inference('demod', [status(thm)], ['8', '9', '10'])).
% 31.19/31.42  thf('401', plain, ((l1_lattices @ sk_A)),
% 31.19/31.42      inference('sup-', [status(thm)], ['12', '13'])).
% 31.19/31.42  thf('402', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.42            = (k4_lattices @ sk_A @ X0 @ sk_C_3))
% 31.19/31.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | (v2_struct_0 @ sk_A))),
% 31.19/31.42      inference('demod', [status(thm)], ['399', '400', '401'])).
% 31.19/31.42  thf('403', plain, (~ (v2_struct_0 @ sk_A)),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('404', plain,
% 31.19/31.42      (![X0 : $i]:
% 31.19/31.42         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 31.19/31.42          | ((k4_lattices @ sk_A @ sk_C_3 @ X0)
% 31.19/31.42              = (k4_lattices @ sk_A @ X0 @ sk_C_3)))),
% 31.19/31.42      inference('clc', [status(thm)], ['402', '403'])).
% 31.19/31.42  thf('405', plain,
% 31.19/31.42      (((k4_lattices @ sk_A @ sk_C_3 @ sk_D_2)
% 31.19/31.42         = (k4_lattices @ sk_A @ sk_D_2 @ sk_C_3))),
% 31.19/31.42      inference('sup-', [status(thm)], ['396', '404'])).
% 31.19/31.42  thf('406', plain,
% 31.19/31.42      (((k4_lattices @ sk_A @ sk_C_3 @ sk_D_2)
% 31.19/31.42         = (k2_lattices @ sk_A @ sk_D_2 @ sk_C_3))),
% 31.19/31.42      inference('demod', [status(thm)], ['395', '405'])).
% 31.19/31.42  thf('407', plain,
% 31.19/31.42      (((sk_D_2)
% 31.19/31.42         = (k1_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_C_3 @ sk_B_3) @ 
% 31.19/31.42            (k4_lattices @ sk_A @ sk_C_3 @ sk_D_2)))),
% 31.19/31.42      inference('demod', [status(thm)], ['282', '287', '392', '406'])).
% 31.19/31.42  thf('408', plain, (((sk_D_2) = (sk_C_3))),
% 31.19/31.42      inference('sup+', [status(thm)], ['256', '407'])).
% 31.19/31.42  thf('409', plain, (((sk_C_3) != (sk_D_2))),
% 31.19/31.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.19/31.42  thf('410', plain, ($false),
% 31.19/31.42      inference('simplify_reflect-', [status(thm)], ['408', '409'])).
% 31.19/31.42  
% 31.19/31.42  % SZS output end Refutation
% 31.19/31.42  
% 31.19/31.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
