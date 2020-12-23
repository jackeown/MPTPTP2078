%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zqXqSgowz6

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:38 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 546 expanded)
%              Number of leaves         :   35 ( 172 expanded)
%              Depth                    :   20
%              Number of atoms          : 1608 (8744 expanded)
%              Number of equality atoms :   49 (  55 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_lattices_type,type,(
    k3_lattices: $i > $i > $i > $i )).

thf(v17_lattices_type,type,(
    v17_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

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
    ~ ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k7_lattices @ X7 @ X8 ) @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_lattices])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(commutativity_k3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k3_lattices @ A @ B @ C )
        = ( k3_lattices @ A @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l2_lattices @ X2 )
      | ~ ( v4_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k3_lattices @ X2 @ X1 @ X3 )
        = ( k3_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_lattices])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
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
      | ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_lattices @ sk_A ),
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
      ( ( l2_lattices @ X9 )
      | ~ ( l3_lattices @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('25',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','22','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k3_lattices @ sk_A @ X0 @ ( k7_lattices @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('31',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l2_lattices @ X11 )
      | ~ ( v4_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k3_lattices @ X11 @ X10 @ X12 )
        = ( k1_lattices @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('35',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,
    ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('42',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l2_lattices @ X11 )
      | ~ ( v4_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k3_lattices @ X11 @ X10 @ X12 )
        = ( k1_lattices @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_lattices])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v4_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('46',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
        = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

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

thf('53',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( ( k1_lattices @ X5 @ X4 @ X6 )
       != X6 )
      | ( r1_lattices @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l2_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
     != ( k7_lattices @ sk_A @ sk_B ) )
    | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('59',plain,
    ( ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
     != ( k7_lattices @ sk_A @ sk_B ) )
    | ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
     != ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v17_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k7_lattices @ A @ ( k4_lattices @ A @ B @ C ) )
                = ( k3_lattices @ A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( ( k7_lattices @ X23 @ ( k4_lattices @ X23 @ X22 @ X24 ) )
        = ( k3_lattices @ X23 @ ( k7_lattices @ X23 @ X22 ) @ ( k7_lattices @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v17_lattices @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t50_lattices])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v17_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ X0 ) )
        = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v17_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ X0 ) )
        = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ X0 ) )
        = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k7_lattices @ sk_A @ ( k4_lattices @ sk_A @ sk_B @ sk_C ) )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('75',plain,(
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

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_lattices @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['76','82','88','89'])).

thf('91',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B @ sk_C )
    | ( ( k2_lattices @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','90'])).

thf('92',plain,(
    r3_lattices @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('94',plain,(
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

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('103',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('104',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r3_lattices @ sk_A @ sk_B @ X0 )
      | ( r1_lattices @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','101','102','103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r1_lattices @ sk_A @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('113',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ~ ( v6_lattices @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( ( k4_lattices @ X14 @ X13 @ X15 )
        = ( k2_lattices @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_lattices])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('116',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X9: $i] :
      ( ( l1_lattices @ X9 )
      | ~ ( l3_lattices @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('118',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ sk_B @ X0 )
        = ( k2_lattices @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ sk_C )
    = ( k2_lattices @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['111','121'])).

thf('123',plain,
    ( ( ( k4_lattices @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','110','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k4_lattices @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k7_lattices @ sk_A @ sk_B )
    = ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','125'])).

thf('127',plain,
    ( ( k3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('128',plain,
    ( ( k7_lattices @ sk_A @ sk_B )
    = ( k1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_B ) @ ( k7_lattices @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) )
    | ( ( k7_lattices @ sk_A @ sk_B )
     != ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','128'])).

thf('130',plain,(
    r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('132',plain,(
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

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('135',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('136',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('137',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k7_lattices @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    r3_lattices @ sk_A @ ( k7_lattices @ sk_A @ sk_C ) @ ( k7_lattices @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['0','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zqXqSgowz6
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:31:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 329 iterations in 0.230s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.51/0.70  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 0.51/0.70  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.51/0.70  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.70  thf(k3_lattices_type, type, k3_lattices: $i > $i > $i > $i).
% 0.51/0.70  thf(v17_lattices_type, type, v17_lattices: $i > $o).
% 0.51/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.70  thf(k4_lattices_type, type, k4_lattices: $i > $i > $i > $i).
% 0.51/0.70  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.51/0.70  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.51/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.70  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.51/0.70  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.51/0.70  thf(k7_lattices_type, type, k7_lattices: $i > $i > $i).
% 0.51/0.70  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.51/0.70  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.51/0.70  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.51/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.70  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.51/0.70  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(t53_lattices, conjecture,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.51/0.70         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70               ( ( r3_lattices @ A @ B @ C ) =>
% 0.51/0.70                 ( r3_lattices @
% 0.51/0.70                   A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i]:
% 0.51/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.51/0.70            ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.51/0.70          ( ![B:$i]:
% 0.51/0.70            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70              ( ![C:$i]:
% 0.51/0.70                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70                  ( ( r3_lattices @ A @ B @ C ) =>
% 0.51/0.70                    ( r3_lattices @
% 0.51/0.70                      A @ ( k7_lattices @ A @ C ) @ ( k7_lattices @ A @ B ) ) ) ) ) ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t53_lattices])).
% 0.51/0.70  thf('0', plain,
% 0.51/0.70      (~ (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70          (k7_lattices @ sk_A @ sk_B))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(dt_k7_lattices, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) & 
% 0.51/0.70         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70       ( m1_subset_1 @ ( k7_lattices @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.51/0.70  thf('2', plain,
% 0.51/0.70      (![X7 : $i, X8 : $i]:
% 0.51/0.70         (~ (l3_lattices @ X7)
% 0.51/0.70          | (v2_struct_0 @ X7)
% 0.51/0.70          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.51/0.70          | (m1_subset_1 @ (k7_lattices @ X7 @ X8) @ (u1_struct_0 @ X7)))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.51/0.70  thf('3', plain,
% 0.51/0.70      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (l3_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.70  thf('4', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.70  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      (![X7 : $i, X8 : $i]:
% 0.51/0.70         (~ (l3_lattices @ X7)
% 0.51/0.70          | (v2_struct_0 @ X7)
% 0.51/0.70          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.51/0.70          | (m1_subset_1 @ (k7_lattices @ X7 @ X8) @ (u1_struct_0 @ X7)))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k7_lattices])).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (l3_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.70  thf('11', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['10', '11'])).
% 0.51/0.70  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf(commutativity_k3_lattices, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.51/0.70         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70       ( ( k3_lattices @ A @ B @ C ) = ( k3_lattices @ A @ C @ B ) ) ))).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.51/0.70          | ~ (l2_lattices @ X2)
% 0.51/0.70          | ~ (v4_lattices @ X2)
% 0.51/0.70          | (v2_struct_0 @ X2)
% 0.51/0.70          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 0.51/0.70          | ((k3_lattices @ X2 @ X1 @ X3) = (k3_lattices @ X2 @ X3 @ X1)))),
% 0.51/0.70      inference('cnf', [status(esa)], [commutativity_k3_lattices])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.51/0.70            = (k3_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B)))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v4_lattices @ sk_A)
% 0.51/0.70          | ~ (l2_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.51/0.70  thf(cc1_lattices, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l3_lattices @ A ) =>
% 0.51/0.70       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.51/0.70         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.51/0.70           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.51/0.70           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ X0)
% 0.51/0.70          | ~ (v10_lattices @ X0)
% 0.51/0.70          | (v4_lattices @ X0)
% 0.51/0.70          | ~ (l3_lattices @ X0))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.51/0.70  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('19', plain,
% 0.51/0.70      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.51/0.70  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('21', plain, ((v10_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('22', plain, ((v4_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.51/0.70  thf('23', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(dt_l3_lattices, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.51/0.70  thf('24', plain, (![X9 : $i]: ((l2_lattices @ X9) | ~ (l3_lattices @ X9))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.51/0.70  thf('25', plain, ((l2_lattices @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.51/0.70            = (k3_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B)))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['16', '22', '25'])).
% 0.51/0.70  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.51/0.70              = (k3_lattices @ sk_A @ X0 @ (k7_lattices @ sk_A @ sk_B))))),
% 0.51/0.70      inference('clc', [status(thm)], ['26', '27'])).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_C))
% 0.51/0.70         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['7', '28'])).
% 0.51/0.70  thf('30', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('31', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf(redefinition_k3_lattices, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.51/0.70         ( l2_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70       ( ( k3_lattices @ A @ B @ C ) = ( k1_lattices @ A @ B @ C ) ) ))).
% 0.51/0.70  thf('32', plain,
% 0.51/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.51/0.70          | ~ (l2_lattices @ X11)
% 0.51/0.70          | ~ (v4_lattices @ X11)
% 0.51/0.70          | (v2_struct_0 @ X11)
% 0.51/0.70          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.51/0.70          | ((k3_lattices @ X11 @ X10 @ X12) = (k1_lattices @ X11 @ X10 @ X12)))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.51/0.70            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v4_lattices @ sk_A)
% 0.51/0.70          | ~ (l2_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.51/0.70  thf('34', plain, ((v4_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.51/0.70  thf('35', plain, ((l2_lattices @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.51/0.70            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.51/0.70  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('38', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)
% 0.51/0.70              = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['36', '37'])).
% 0.51/0.70  thf('39', plain,
% 0.51/0.70      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_C))
% 0.51/0.70         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_C)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['30', '38'])).
% 0.51/0.70  thf('40', plain,
% 0.51/0.70      (((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_C))
% 0.51/0.70         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '39'])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf('42', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('43', plain,
% 0.51/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.51/0.70          | ~ (l2_lattices @ X11)
% 0.51/0.70          | ~ (v4_lattices @ X11)
% 0.51/0.70          | (v2_struct_0 @ X11)
% 0.51/0.70          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.51/0.70          | ((k3_lattices @ X11 @ X10 @ X12) = (k1_lattices @ X11 @ X10 @ X12)))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k3_lattices])).
% 0.51/0.70  thf('44', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v4_lattices @ sk_A)
% 0.51/0.70          | ~ (l2_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.51/0.70  thf('45', plain, ((v4_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.51/0.70  thf('46', plain, ((l2_lattices @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.70  thf('47', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70            = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.51/0.70  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('49', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70              = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['47', '48'])).
% 0.51/0.70  thf('50', plain,
% 0.51/0.70      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_B))
% 0.51/0.70         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['41', '49'])).
% 0.51/0.70  thf('51', plain,
% 0.51/0.70      (((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_C))
% 0.51/0.70         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup+', [status(thm)], ['40', '50'])).
% 0.51/0.70  thf('52', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf(d3_lattices, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.51/0.70                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf('53', plain,
% 0.51/0.70      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.51/0.70          | ((k1_lattices @ X5 @ X4 @ X6) != (X6))
% 0.51/0.70          | (r1_lattices @ X5 @ X4 @ X6)
% 0.51/0.70          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.51/0.70          | ~ (l2_lattices @ X5)
% 0.51/0.70          | (v2_struct_0 @ X5))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_lattices])).
% 0.51/0.70  thf('54', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (l2_lattices @ sk_A)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70          | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0) != (X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['52', '53'])).
% 0.51/0.70  thf('55', plain, ((l2_lattices @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.70  thf('56', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70          | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0) != (X0)))),
% 0.51/0.70      inference('demod', [status(thm)], ['54', '55'])).
% 0.51/0.70  thf('57', plain,
% 0.51/0.70      ((((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70          (k7_lattices @ sk_A @ sk_C)) != (k7_lattices @ sk_A @ sk_B))
% 0.51/0.70        | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70           (k7_lattices @ sk_A @ sk_B))
% 0.51/0.70        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['51', '56'])).
% 0.51/0.70  thf('58', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf('59', plain,
% 0.51/0.70      ((((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70          (k7_lattices @ sk_A @ sk_C)) != (k7_lattices @ sk_A @ sk_B))
% 0.51/0.70        | (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70           (k7_lattices @ sk_A @ sk_B))
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.70  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('61', plain,
% 0.51/0.70      (((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_B))
% 0.51/0.70        | ((k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_C)) != (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('clc', [status(thm)], ['59', '60'])).
% 0.51/0.70  thf('62', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(t50_lattices, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.51/0.70         ( v17_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70               ( ( k7_lattices @ A @ ( k4_lattices @ A @ B @ C ) ) =
% 0.51/0.70                 ( k3_lattices @
% 0.51/0.70                   A @ ( k7_lattices @ A @ B ) @ ( k7_lattices @ A @ C ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf('64', plain,
% 0.51/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.51/0.70          | ((k7_lattices @ X23 @ (k4_lattices @ X23 @ X22 @ X24))
% 0.51/0.70              = (k3_lattices @ X23 @ (k7_lattices @ X23 @ X22) @ 
% 0.51/0.70                 (k7_lattices @ X23 @ X24)))
% 0.51/0.70          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.51/0.70          | ~ (l3_lattices @ X23)
% 0.51/0.70          | ~ (v17_lattices @ X23)
% 0.51/0.70          | ~ (v10_lattices @ X23)
% 0.51/0.70          | (v2_struct_0 @ X23))),
% 0.51/0.70      inference('cnf', [status(esa)], [t50_lattices])).
% 0.51/0.70  thf('65', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v10_lattices @ sk_A)
% 0.51/0.70          | ~ (v17_lattices @ sk_A)
% 0.51/0.70          | ~ (l3_lattices @ sk_A)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k7_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B @ X0))
% 0.51/0.70              = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70                 (k7_lattices @ sk_A @ X0))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['63', '64'])).
% 0.51/0.70  thf('66', plain, ((v10_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('67', plain, ((v17_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('68', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('69', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k7_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B @ X0))
% 0.51/0.70              = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70                 (k7_lattices @ sk_A @ X0))))),
% 0.51/0.70      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.51/0.70  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('71', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k7_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B @ X0))
% 0.51/0.70            = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70               (k7_lattices @ sk_A @ X0)))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.70      inference('clc', [status(thm)], ['69', '70'])).
% 0.51/0.70  thf('72', plain,
% 0.51/0.70      (((k7_lattices @ sk_A @ (k4_lattices @ sk_A @ sk_B @ sk_C))
% 0.51/0.70         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_C)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['62', '71'])).
% 0.51/0.70  thf('73', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('74', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(t21_lattices, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.51/0.70         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70           ( ![C:$i]:
% 0.51/0.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.70               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.51/0.70                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf('75', plain,
% 0.51/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.51/0.70          | ~ (r1_lattices @ X20 @ X19 @ X21)
% 0.51/0.70          | ((k2_lattices @ X20 @ X19 @ X21) = (X19))
% 0.51/0.70          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.51/0.70          | ~ (l3_lattices @ X20)
% 0.51/0.70          | ~ (v9_lattices @ X20)
% 0.51/0.70          | ~ (v8_lattices @ X20)
% 0.51/0.70          | (v2_struct_0 @ X20))),
% 0.51/0.70      inference('cnf', [status(esa)], [t21_lattices])).
% 0.51/0.70  thf('76', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v8_lattices @ sk_A)
% 0.51/0.70          | ~ (v9_lattices @ sk_A)
% 0.51/0.70          | ~ (l3_lattices @ sk_A)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k2_lattices @ sk_A @ sk_B @ X0) = (sk_B))
% 0.51/0.70          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['74', '75'])).
% 0.51/0.70  thf('77', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ X0)
% 0.51/0.70          | ~ (v10_lattices @ X0)
% 0.51/0.70          | (v8_lattices @ X0)
% 0.51/0.70          | ~ (l3_lattices @ X0))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.51/0.70  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('79', plain,
% 0.51/0.70      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['77', '78'])).
% 0.51/0.70  thf('80', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('81', plain, ((v10_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('82', plain, ((v8_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.51/0.70  thf('83', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ X0)
% 0.51/0.70          | ~ (v10_lattices @ X0)
% 0.51/0.70          | (v9_lattices @ X0)
% 0.51/0.70          | ~ (l3_lattices @ X0))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.51/0.70  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('85', plain,
% 0.51/0.70      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['83', '84'])).
% 0.51/0.70  thf('86', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('87', plain, ((v10_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('88', plain, ((v9_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.51/0.70  thf('89', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('90', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k2_lattices @ sk_A @ sk_B @ X0) = (sk_B))
% 0.51/0.70          | ~ (r1_lattices @ sk_A @ sk_B @ X0))),
% 0.51/0.70      inference('demod', [status(thm)], ['76', '82', '88', '89'])).
% 0.51/0.70  thf('91', plain,
% 0.51/0.70      ((~ (r1_lattices @ sk_A @ sk_B @ sk_C)
% 0.51/0.70        | ((k2_lattices @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.51/0.70        | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['73', '90'])).
% 0.51/0.70  thf('92', plain, ((r3_lattices @ sk_A @ sk_B @ sk_C)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('93', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(redefinition_r3_lattices, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.51/0.70         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 0.51/0.70         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 0.51/0.70  thf('94', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.51/0.70          | ~ (l3_lattices @ X17)
% 0.51/0.70          | ~ (v9_lattices @ X17)
% 0.51/0.70          | ~ (v8_lattices @ X17)
% 0.51/0.70          | ~ (v6_lattices @ X17)
% 0.51/0.70          | (v2_struct_0 @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.51/0.70          | (r1_lattices @ X17 @ X16 @ X18)
% 0.51/0.70          | ~ (r3_lattices @ X17 @ X16 @ X18))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.51/0.70  thf('95', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.51/0.70          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v6_lattices @ sk_A)
% 0.51/0.70          | ~ (v8_lattices @ sk_A)
% 0.51/0.70          | ~ (v9_lattices @ sk_A)
% 0.51/0.70          | ~ (l3_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['93', '94'])).
% 0.51/0.70  thf('96', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((v2_struct_0 @ X0)
% 0.51/0.70          | ~ (v10_lattices @ X0)
% 0.51/0.70          | (v6_lattices @ X0)
% 0.51/0.70          | ~ (l3_lattices @ X0))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.51/0.70  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('98', plain,
% 0.51/0.70      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['96', '97'])).
% 0.51/0.70  thf('99', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('100', plain, ((v10_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('101', plain, ((v6_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.51/0.70  thf('102', plain, ((v8_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.51/0.70  thf('103', plain, ((v9_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.51/0.70  thf('104', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('105', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r3_lattices @ sk_A @ sk_B @ X0)
% 0.51/0.70          | (r1_lattices @ sk_A @ sk_B @ X0)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['95', '101', '102', '103', '104'])).
% 0.51/0.70  thf('106', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (r1_lattices @ sk_A @ sk_B @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['92', '105'])).
% 0.51/0.70  thf('107', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('108', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_A) | (r1_lattices @ sk_A @ sk_B @ sk_C))),
% 0.51/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.51/0.70  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('110', plain, ((r1_lattices @ sk_A @ sk_B @ sk_C)),
% 0.51/0.70      inference('clc', [status(thm)], ['108', '109'])).
% 0.51/0.70  thf('111', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('112', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(redefinition_k4_lattices, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.51/0.70         ( l1_lattices @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70       ( ( k4_lattices @ A @ B @ C ) = ( k2_lattices @ A @ B @ C ) ) ))).
% 0.51/0.70  thf('113', plain,
% 0.51/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.51/0.70          | ~ (l1_lattices @ X14)
% 0.51/0.70          | ~ (v6_lattices @ X14)
% 0.51/0.70          | (v2_struct_0 @ X14)
% 0.51/0.70          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.51/0.70          | ((k4_lattices @ X14 @ X13 @ X15) = (k2_lattices @ X14 @ X13 @ X15)))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k4_lattices])).
% 0.51/0.70  thf('114', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k4_lattices @ sk_A @ sk_B @ X0) = (k2_lattices @ sk_A @ sk_B @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v6_lattices @ sk_A)
% 0.51/0.70          | ~ (l1_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.51/0.70  thf('115', plain, ((v6_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.51/0.70  thf('116', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('117', plain, (![X9 : $i]: ((l1_lattices @ X9) | ~ (l3_lattices @ X9))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.51/0.70  thf('118', plain, ((l1_lattices @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['116', '117'])).
% 0.51/0.70  thf('119', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k4_lattices @ sk_A @ sk_B @ X0) = (k2_lattices @ sk_A @ sk_B @ X0))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['114', '115', '118'])).
% 0.51/0.70  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('121', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | ((k4_lattices @ sk_A @ sk_B @ X0)
% 0.51/0.70              = (k2_lattices @ sk_A @ sk_B @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['119', '120'])).
% 0.51/0.70  thf('122', plain,
% 0.51/0.70      (((k4_lattices @ sk_A @ sk_B @ sk_C) = (k2_lattices @ sk_A @ sk_B @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['111', '121'])).
% 0.51/0.70  thf('123', plain,
% 0.51/0.70      ((((k4_lattices @ sk_A @ sk_B @ sk_C) = (sk_B)) | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['91', '110', '122'])).
% 0.51/0.70  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('125', plain, (((k4_lattices @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.51/0.70      inference('clc', [status(thm)], ['123', '124'])).
% 0.51/0.70  thf('126', plain,
% 0.51/0.70      (((k7_lattices @ sk_A @ sk_B)
% 0.51/0.70         = (k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_C)))),
% 0.51/0.70      inference('demod', [status(thm)], ['72', '125'])).
% 0.51/0.70  thf('127', plain,
% 0.51/0.70      (((k3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_C))
% 0.51/0.70         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_C)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['30', '38'])).
% 0.51/0.70  thf('128', plain,
% 0.51/0.70      (((k7_lattices @ sk_A @ sk_B)
% 0.51/0.70         = (k1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_B) @ 
% 0.51/0.70            (k7_lattices @ sk_A @ sk_C)))),
% 0.51/0.70      inference('sup+', [status(thm)], ['126', '127'])).
% 0.51/0.70  thf('129', plain,
% 0.51/0.70      (((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70         (k7_lattices @ sk_A @ sk_B))
% 0.51/0.70        | ((k7_lattices @ sk_A @ sk_B) != (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['61', '128'])).
% 0.51/0.70  thf('130', plain,
% 0.51/0.70      ((r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70        (k7_lattices @ sk_A @ sk_B))),
% 0.51/0.70      inference('simplify', [status(thm)], ['129'])).
% 0.51/0.70  thf('131', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('132', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.51/0.70          | ~ (l3_lattices @ X17)
% 0.51/0.70          | ~ (v9_lattices @ X17)
% 0.51/0.70          | ~ (v8_lattices @ X17)
% 0.51/0.70          | ~ (v6_lattices @ X17)
% 0.51/0.70          | (v2_struct_0 @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.51/0.70          | (r3_lattices @ X17 @ X16 @ X18)
% 0.51/0.70          | ~ (r1_lattices @ X17 @ X16 @ X18))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 0.51/0.70  thf('133', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A)
% 0.51/0.70          | ~ (v6_lattices @ sk_A)
% 0.51/0.70          | ~ (v8_lattices @ sk_A)
% 0.51/0.70          | ~ (v9_lattices @ sk_A)
% 0.51/0.70          | ~ (l3_lattices @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['131', '132'])).
% 0.51/0.70  thf('134', plain, ((v6_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.51/0.70  thf('135', plain, ((v8_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.51/0.70  thf('136', plain, ((v9_lattices @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.51/0.70  thf('137', plain, ((l3_lattices @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('138', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r1_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70          | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ X0)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.51/0.70          | (v2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['133', '134', '135', '136', '137'])).
% 0.51/0.70  thf('139', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_A)
% 0.51/0.70        | ~ (m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.51/0.70        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70           (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['130', '138'])).
% 0.51/0.70  thf('140', plain,
% 0.51/0.70      ((m1_subset_1 @ (k7_lattices @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.51/0.70      inference('clc', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf('141', plain,
% 0.51/0.70      (((v2_struct_0 @ sk_A)
% 0.51/0.70        | (r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70           (k7_lattices @ sk_A @ sk_B)))),
% 0.51/0.70      inference('demod', [status(thm)], ['139', '140'])).
% 0.51/0.70  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('143', plain,
% 0.51/0.70      ((r3_lattices @ sk_A @ (k7_lattices @ sk_A @ sk_C) @ 
% 0.51/0.70        (k7_lattices @ sk_A @ sk_B))),
% 0.51/0.70      inference('clc', [status(thm)], ['141', '142'])).
% 0.51/0.70  thf('144', plain, ($false), inference('demod', [status(thm)], ['0', '143'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
