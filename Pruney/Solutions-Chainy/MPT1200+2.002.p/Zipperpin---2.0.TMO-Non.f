%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7K0UA0MMzk

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:31 EST 2020

% Result     : Timeout 58.38s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   94 ( 194 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  975 (3674 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(t27_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_lattices @ A @ B @ C )
                   => ( r1_lattices @ A @ ( k2_lattices @ A @ B @ D ) @ ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r1_lattices @ A @ B @ C )
                     => ( r1_lattices @ A @ ( k2_lattices @ A @ B @ D ) @ ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_lattices])).

thf('0',plain,(
    ~ ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k2_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k2_lattices @ X11 @ X10 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattices])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( l1_lattices @ X13 )
      | ~ ( l3_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('8',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','11'])).

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

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v8_lattices @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k1_lattices @ X7 @ ( k2_lattices @ X7 @ X9 @ X8 ) @ X8 )
        = X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l3_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_lattices])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
        = ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
      | ~ ( v8_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
        = ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
        = ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
    = ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_lattices @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k2_lattices @ X11 @ X10 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_lattices])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','28'])).

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

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ X0 @ X2 )
       != X2 )
      | ( r1_lattices @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l2_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ X0 )
       != X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X13: $i] :
      ( ( l2_lattices @ X13 )
      | ~ ( l3_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('34',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ X0 )
      | ( ( k1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ X0 )
       != X0 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
     != ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('38',plain,
    ( ( ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 )
     != ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v7_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( k2_lattices @ A @ B @ ( k2_lattices @ A @ C @ D ) )
                      = ( k2_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( v7_lattices @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( ( k2_lattices @ X3 @ X5 @ ( k2_lattices @ X3 @ X4 @ X6 ) )
        = ( k2_lattices @ X3 @ ( k2_lattices @ X3 @ X5 @ X4 ) @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_lattices @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_lattices])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_2 @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ X1 ) )
      | ~ ( v7_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('48',plain,(
    v7_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k2_lattices @ sk_A @ sk_C_2 @ X1 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ X0 @ sk_C_2 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
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

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_lattices @ X15 @ X14 @ X16 )
      | ( ( k2_lattices @ X15 @ X14 @ X16 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v9_lattices @ X15 )
      | ~ ( v8_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
        = sk_B_2 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v8_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v9_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
        = sk_B_2 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    | ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    r1_lattices @ sk_A @ sk_B_2 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
      = sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_C_2 )
    = sk_B_2 ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ X0 ) )
        = ( k2_lattices @ sk_A @ sk_B_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) )
    = ( k2_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('68',plain,(
    r1_lattices @ sk_A @ ( k2_lattices @ sk_A @ sk_B_2 @ sk_D_1 ) @ ( k2_lattices @ sk_A @ sk_C_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['41','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7K0UA0MMzk
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:42:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 58.38/58.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 58.38/58.59  % Solved by: fo/fo7.sh
% 58.38/58.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 58.38/58.59  % done 4296 iterations in 58.123s
% 58.38/58.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 58.38/58.59  % SZS output start Refutation
% 58.38/58.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 58.38/58.59  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 58.38/58.59  thf(sk_A_type, type, sk_A: $i).
% 58.38/58.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 58.38/58.59  thf(sk_B_2_type, type, sk_B_2: $i).
% 58.38/58.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 58.38/58.59  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 58.38/58.59  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 58.38/58.59  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 58.38/58.59  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 58.38/58.59  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 58.38/58.59  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 58.38/58.59  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 58.38/58.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 58.38/58.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 58.38/58.59  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 58.38/58.59  thf(t27_lattices, conjecture,
% 58.38/58.59    (![A:$i]:
% 58.38/58.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_lattices @ A ) & 
% 58.38/58.59         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 58.38/58.59       ( ![B:$i]:
% 58.38/58.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59           ( ![C:$i]:
% 58.38/58.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59               ( ![D:$i]:
% 58.38/58.59                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59                   ( ( r1_lattices @ A @ B @ C ) =>
% 58.38/58.59                     ( r1_lattices @
% 58.38/58.59                       A @ ( k2_lattices @ A @ B @ D ) @ 
% 58.38/58.59                       ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 58.38/58.59  thf(zf_stmt_0, negated_conjecture,
% 58.38/58.59    (~( ![A:$i]:
% 58.38/58.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_lattices @ A ) & 
% 58.38/58.59            ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 58.38/58.59          ( ![B:$i]:
% 58.38/58.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59              ( ![C:$i]:
% 58.38/58.59                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59                  ( ![D:$i]:
% 58.38/58.59                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59                      ( ( r1_lattices @ A @ B @ C ) =>
% 58.38/58.59                        ( r1_lattices @
% 58.38/58.59                          A @ ( k2_lattices @ A @ B @ D ) @ 
% 58.38/58.59                          ( k2_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 58.38/58.59    inference('cnf.neg', [status(esa)], [t27_lattices])).
% 58.38/58.59  thf('0', plain,
% 58.38/58.59      (~ (r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_D_1) @ 
% 58.38/58.59          (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('2', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('3', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf(dt_k2_lattices, axiom,
% 58.38/58.59    (![A:$i,B:$i,C:$i]:
% 58.38/58.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) & 
% 58.38/58.59         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 58.38/58.59         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 58.38/58.59       ( m1_subset_1 @ ( k2_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 58.38/58.59  thf('4', plain,
% 58.38/58.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 58.38/58.59         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 58.38/58.59          | ~ (l1_lattices @ X11)
% 58.38/58.59          | (v2_struct_0 @ X11)
% 58.38/58.59          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 58.38/58.59          | (m1_subset_1 @ (k2_lattices @ X11 @ X10 @ X12) @ 
% 58.38/58.59             (u1_struct_0 @ X11)))),
% 58.38/58.59      inference('cnf', [status(esa)], [dt_k2_lattices])).
% 58.38/58.59  thf('5', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_2 @ X0) @ 
% 58.38/58.59           (u1_struct_0 @ sk_A))
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (l1_lattices @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['3', '4'])).
% 58.38/58.59  thf('6', plain, ((l3_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf(dt_l3_lattices, axiom,
% 58.38/58.59    (![A:$i]:
% 58.38/58.59     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 58.38/58.59  thf('7', plain, (![X13 : $i]: ((l1_lattices @ X13) | ~ (l3_lattices @ X13))),
% 58.38/58.59      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 58.38/58.59  thf('8', plain, ((l1_lattices @ sk_A)),
% 58.38/58.59      inference('sup-', [status(thm)], ['6', '7'])).
% 58.38/58.59  thf('9', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_2 @ X0) @ 
% 58.38/58.59           (u1_struct_0 @ sk_A))
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('demod', [status(thm)], ['5', '8'])).
% 58.38/58.59  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('11', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_2 @ X0) @ 
% 58.38/58.59             (u1_struct_0 @ sk_A)))),
% 58.38/58.59      inference('clc', [status(thm)], ['9', '10'])).
% 58.38/58.59  thf('12', plain,
% 58.38/58.59      ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1) @ 
% 58.38/58.59        (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['2', '11'])).
% 58.38/58.59  thf(d8_lattices, axiom,
% 58.38/58.59    (![A:$i]:
% 58.38/58.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 58.38/58.59       ( ( v8_lattices @ A ) <=>
% 58.38/58.59         ( ![B:$i]:
% 58.38/58.59           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59             ( ![C:$i]:
% 58.38/58.59               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59                 ( ( k1_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ C ) =
% 58.38/58.59                   ( C ) ) ) ) ) ) ) ))).
% 58.38/58.59  thf('13', plain,
% 58.38/58.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 58.38/58.59         (~ (v8_lattices @ X7)
% 58.38/58.59          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 58.38/58.59          | ((k1_lattices @ X7 @ (k2_lattices @ X7 @ X9 @ X8) @ X8) = (X8))
% 58.38/58.59          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 58.38/58.59          | ~ (l3_lattices @ X7)
% 58.38/58.59          | (v2_struct_0 @ X7))),
% 58.38/58.59      inference('cnf', [status(esa)], [d8_lattices])).
% 58.38/58.59  thf('14', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (l3_lattices @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ((k1_lattices @ sk_A @ 
% 58.38/58.59              (k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59              (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59              = (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59          | ~ (v8_lattices @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['12', '13'])).
% 58.38/58.59  thf('15', plain, ((l3_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('16', plain, ((v8_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('17', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ((k1_lattices @ sk_A @ 
% 58.38/58.59              (k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59              (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59              = (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 58.38/58.59      inference('demod', [status(thm)], ['14', '15', '16'])).
% 58.38/58.59  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('19', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         (((k1_lattices @ sk_A @ 
% 58.38/58.59            (k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59            (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59            = (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 58.38/58.59      inference('clc', [status(thm)], ['17', '18'])).
% 58.38/58.59  thf('20', plain,
% 58.38/58.59      (((k1_lattices @ sk_A @ 
% 58.38/58.59         (k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59         (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59         = (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))),
% 58.38/58.59      inference('sup-', [status(thm)], ['1', '19'])).
% 58.38/58.59  thf('21', plain,
% 58.38/58.59      ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1) @ 
% 58.38/58.59        (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['2', '11'])).
% 58.38/58.59  thf('22', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('23', plain,
% 58.38/58.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 58.38/58.59         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 58.38/58.59          | ~ (l1_lattices @ X11)
% 58.38/58.59          | (v2_struct_0 @ X11)
% 58.38/58.59          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 58.38/58.59          | (m1_subset_1 @ (k2_lattices @ X11 @ X10 @ X12) @ 
% 58.38/58.59             (u1_struct_0 @ X11)))),
% 58.38/58.59      inference('cnf', [status(esa)], [dt_k2_lattices])).
% 58.38/58.59  thf('24', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 58.38/58.59           (u1_struct_0 @ sk_A))
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (l1_lattices @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['22', '23'])).
% 58.38/58.59  thf('25', plain, ((l1_lattices @ sk_A)),
% 58.38/58.59      inference('sup-', [status(thm)], ['6', '7'])).
% 58.38/58.59  thf('26', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 58.38/58.59           (u1_struct_0 @ sk_A))
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('demod', [status(thm)], ['24', '25'])).
% 58.38/58.59  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('28', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (m1_subset_1 @ (k2_lattices @ sk_A @ sk_B_2 @ X0) @ 
% 58.38/58.59             (u1_struct_0 @ sk_A)))),
% 58.38/58.59      inference('clc', [status(thm)], ['26', '27'])).
% 58.38/58.59  thf('29', plain,
% 58.38/58.59      ((m1_subset_1 @ 
% 58.38/58.59        (k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59        (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['21', '28'])).
% 58.38/58.59  thf(d3_lattices, axiom,
% 58.38/58.59    (![A:$i]:
% 58.38/58.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 58.38/58.59       ( ![B:$i]:
% 58.38/58.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59           ( ![C:$i]:
% 58.38/58.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59               ( ( r1_lattices @ A @ B @ C ) <=>
% 58.38/58.59                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 58.38/58.59  thf('30', plain,
% 58.38/58.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 58.38/58.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 58.38/58.59          | ((k1_lattices @ X1 @ X0 @ X2) != (X2))
% 58.38/58.59          | (r1_lattices @ X1 @ X0 @ X2)
% 58.38/58.59          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 58.38/58.59          | ~ (l2_lattices @ X1)
% 58.38/58.59          | (v2_struct_0 @ X1))),
% 58.38/58.59      inference('cnf', [status(esa)], [d3_lattices])).
% 58.38/58.59  thf('31', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (l2_lattices @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (r1_lattices @ sk_A @ 
% 58.38/58.59             (k2_lattices @ sk_A @ sk_B_2 @ 
% 58.38/58.59              (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59             X0)
% 58.38/58.59          | ((k1_lattices @ sk_A @ 
% 58.38/58.59              (k2_lattices @ sk_A @ sk_B_2 @ 
% 58.38/58.59               (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59              X0) != (X0)))),
% 58.38/58.59      inference('sup-', [status(thm)], ['29', '30'])).
% 58.38/58.59  thf('32', plain, ((l3_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('33', plain,
% 58.38/58.59      (![X13 : $i]: ((l2_lattices @ X13) | ~ (l3_lattices @ X13))),
% 58.38/58.59      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 58.38/58.59  thf('34', plain, ((l2_lattices @ sk_A)),
% 58.38/58.59      inference('sup-', [status(thm)], ['32', '33'])).
% 58.38/58.59  thf('35', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (r1_lattices @ sk_A @ 
% 58.38/58.59             (k2_lattices @ sk_A @ sk_B_2 @ 
% 58.38/58.59              (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59             X0)
% 58.38/58.59          | ((k1_lattices @ sk_A @ 
% 58.38/58.59              (k2_lattices @ sk_A @ sk_B_2 @ 
% 58.38/58.59               (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59              X0) != (X0)))),
% 58.38/58.59      inference('demod', [status(thm)], ['31', '34'])).
% 58.38/58.59  thf('36', plain,
% 58.38/58.59      ((((k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 58.38/58.59          != (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59        | (r1_lattices @ sk_A @ 
% 58.38/58.59           (k2_lattices @ sk_A @ sk_B_2 @ 
% 58.38/58.59            (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59           (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59        | ~ (m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1) @ 
% 58.38/58.59             (u1_struct_0 @ sk_A))
% 58.38/58.59        | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['20', '35'])).
% 58.38/58.59  thf('37', plain,
% 58.38/58.59      ((m1_subset_1 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1) @ 
% 58.38/58.59        (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['2', '11'])).
% 58.38/58.59  thf('38', plain,
% 58.38/58.59      ((((k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)
% 58.38/58.59          != (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59        | (r1_lattices @ sk_A @ 
% 58.38/58.59           (k2_lattices @ sk_A @ sk_B_2 @ 
% 58.38/58.59            (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59           (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59        | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('demod', [status(thm)], ['36', '37'])).
% 58.38/58.59  thf('39', plain,
% 58.38/58.59      (((v2_struct_0 @ sk_A)
% 58.38/58.59        | (r1_lattices @ sk_A @ 
% 58.38/58.59           (k2_lattices @ sk_A @ sk_B_2 @ 
% 58.38/58.59            (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59           (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)))),
% 58.38/58.59      inference('simplify', [status(thm)], ['38'])).
% 58.38/58.59  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('41', plain,
% 58.38/58.59      ((r1_lattices @ sk_A @ 
% 58.38/58.59        (k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1)) @ 
% 58.38/58.59        (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))),
% 58.38/58.59      inference('clc', [status(thm)], ['39', '40'])).
% 58.38/58.59  thf('42', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('43', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('44', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf(d7_lattices, axiom,
% 58.38/58.59    (![A:$i]:
% 58.38/58.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 58.38/58.59       ( ( v7_lattices @ A ) <=>
% 58.38/58.59         ( ![B:$i]:
% 58.38/58.59           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59             ( ![C:$i]:
% 58.38/58.59               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59                 ( ![D:$i]:
% 58.38/58.59                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59                     ( ( k2_lattices @ A @ B @ ( k2_lattices @ A @ C @ D ) ) =
% 58.38/58.59                       ( k2_lattices @ A @ ( k2_lattices @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 58.38/58.59  thf('45', plain,
% 58.38/58.59      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 58.38/58.59         (~ (v7_lattices @ X3)
% 58.38/58.59          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 58.38/58.59          | ((k2_lattices @ X3 @ X5 @ (k2_lattices @ X3 @ X4 @ X6))
% 58.38/58.59              = (k2_lattices @ X3 @ (k2_lattices @ X3 @ X5 @ X4) @ X6))
% 58.38/58.59          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X3))
% 58.38/58.59          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X3))
% 58.38/58.59          | ~ (l1_lattices @ X3)
% 58.38/58.59          | (v2_struct_0 @ X3))),
% 58.38/58.59      inference('cnf', [status(esa)], [d7_lattices])).
% 58.38/58.59  thf('46', plain,
% 58.38/58.59      (![X0 : $i, X1 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (l1_lattices @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ((k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_2 @ X1))
% 58.38/58.59              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_2) @ X1))
% 58.38/58.59          | ~ (v7_lattices @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['44', '45'])).
% 58.38/58.59  thf('47', plain, ((l1_lattices @ sk_A)),
% 58.38/58.59      inference('sup-', [status(thm)], ['6', '7'])).
% 58.38/58.59  thf('48', plain, ((v7_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('49', plain,
% 58.38/58.59      (![X0 : $i, X1 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ((k2_lattices @ sk_A @ X0 @ (k2_lattices @ sk_A @ sk_C_2 @ X1))
% 58.38/58.59              = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ X0 @ sk_C_2) @ X1)))),
% 58.38/58.59      inference('demod', [status(thm)], ['46', '47', '48'])).
% 58.38/58.59  thf('50', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         (((k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 58.38/58.59            = (k2_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) @ X0))
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['43', '49'])).
% 58.38/58.59  thf('51', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('52', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf(t21_lattices, axiom,
% 58.38/58.59    (![A:$i]:
% 58.38/58.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 58.38/58.59         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 58.38/58.59       ( ![B:$i]:
% 58.38/58.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59           ( ![C:$i]:
% 58.38/58.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 58.38/58.59               ( ( r1_lattices @ A @ B @ C ) <=>
% 58.38/58.59                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 58.38/58.59  thf('53', plain,
% 58.38/58.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 58.38/58.59         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 58.38/58.59          | ~ (r1_lattices @ X15 @ X14 @ X16)
% 58.38/58.59          | ((k2_lattices @ X15 @ X14 @ X16) = (X14))
% 58.38/58.59          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 58.38/58.59          | ~ (l3_lattices @ X15)
% 58.38/58.59          | ~ (v9_lattices @ X15)
% 58.38/58.59          | ~ (v8_lattices @ X15)
% 58.38/58.59          | (v2_struct_0 @ X15))),
% 58.38/58.59      inference('cnf', [status(esa)], [t21_lattices])).
% 58.38/58.59  thf('54', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (v8_lattices @ sk_A)
% 58.38/58.59          | ~ (v9_lattices @ sk_A)
% 58.38/58.59          | ~ (l3_lattices @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) = (sk_B_2))
% 58.38/58.59          | ~ (r1_lattices @ sk_A @ sk_B_2 @ X0))),
% 58.38/58.59      inference('sup-', [status(thm)], ['52', '53'])).
% 58.38/58.59  thf('55', plain, ((v8_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('56', plain, ((v9_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('57', plain, ((l3_lattices @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('58', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         ((v2_struct_0 @ sk_A)
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) = (sk_B_2))
% 58.38/58.59          | ~ (r1_lattices @ sk_A @ sk_B_2 @ X0))),
% 58.38/58.59      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 58.38/58.59  thf('59', plain,
% 58.38/58.59      ((~ (r1_lattices @ sk_A @ sk_B_2 @ sk_C_2)
% 58.38/58.59        | ((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (sk_B_2))
% 58.38/58.59        | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('sup-', [status(thm)], ['51', '58'])).
% 58.38/58.59  thf('60', plain, ((r1_lattices @ sk_A @ sk_B_2 @ sk_C_2)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('61', plain,
% 58.38/58.59      ((((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (sk_B_2))
% 58.38/58.59        | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('demod', [status(thm)], ['59', '60'])).
% 58.38/58.59  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('63', plain, (((k2_lattices @ sk_A @ sk_B_2 @ sk_C_2) = (sk_B_2))),
% 58.38/58.59      inference('clc', [status(thm)], ['61', '62'])).
% 58.38/58.59  thf('64', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         (((k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 58.38/58.59            = (k2_lattices @ sk_A @ sk_B_2 @ X0))
% 58.38/58.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | (v2_struct_0 @ sk_A))),
% 58.38/58.59      inference('demod', [status(thm)], ['50', '63'])).
% 58.38/58.59  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 58.38/58.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.38/58.59  thf('66', plain,
% 58.38/58.59      (![X0 : $i]:
% 58.38/58.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 58.38/58.59          | ((k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ X0))
% 58.38/58.59              = (k2_lattices @ sk_A @ sk_B_2 @ X0)))),
% 58.38/58.59      inference('clc', [status(thm)], ['64', '65'])).
% 58.38/58.59  thf('67', plain,
% 58.38/58.59      (((k2_lattices @ sk_A @ sk_B_2 @ (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))
% 58.38/58.59         = (k2_lattices @ sk_A @ sk_B_2 @ sk_D_1))),
% 58.38/58.59      inference('sup-', [status(thm)], ['42', '66'])).
% 58.38/58.59  thf('68', plain,
% 58.38/58.59      ((r1_lattices @ sk_A @ (k2_lattices @ sk_A @ sk_B_2 @ sk_D_1) @ 
% 58.38/58.59        (k2_lattices @ sk_A @ sk_C_2 @ sk_D_1))),
% 58.38/58.59      inference('demod', [status(thm)], ['41', '67'])).
% 58.38/58.59  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 58.38/58.59  
% 58.38/58.59  % SZS output end Refutation
% 58.38/58.59  
% 58.44/58.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
