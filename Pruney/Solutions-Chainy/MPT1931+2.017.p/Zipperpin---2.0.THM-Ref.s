%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YuqXWraskS

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:58 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 174 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :   21
%              Number of atoms          : 1012 (1803 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k6_subset_1 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_subset_1 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('21',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ( r1_waybel_0 @ X29 @ X28 @ ( k6_subset_1 @ ( u1_struct_0 @ X29 ) @ X30 ) )
      | ( r2_waybel_0 @ X29 @ X28 @ X30 )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ( m1_subset_1 @ ( sk_D_1 @ X24 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ( r2_waybel_0 @ X23 @ X22 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ~ ( r2_waybel_0 @ X23 @ X22 @ X26 )
      | ( r2_hidden @ ( k2_waybel_0 @ X23 @ X22 @ ( sk_E @ X27 @ X26 @ X22 @ X23 ) ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X2 @ sk_B_2 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_2 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_2 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X2 @ sk_B_2 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X1 @ sk_B_2 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X1 @ sk_B_2 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X1 @ sk_B_2 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D_1 @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_D_1 @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X1: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_2 @ X1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('52',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('53',plain,(
    ! [X22: $i,X23: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ~ ( r2_waybel_0 @ X23 @ X22 @ X26 )
      | ( r2_hidden @ ( k2_waybel_0 @ X23 @ X22 @ ( sk_E @ X27 @ X26 @ X22 @ X23 ) ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_B_1 @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('64',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference('sup-',[status(thm)],['62','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YuqXWraskS
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.90  % Solved by: fo/fo7.sh
% 0.68/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.90  % done 760 iterations in 0.424s
% 0.68/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.90  % SZS output start Refutation
% 0.68/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.90  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.68/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.90  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.68/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.90  thf(sk_B_type, type, sk_B: $i > $i).
% 0.68/0.90  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.68/0.90  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.90  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.68/0.90  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.68/0.90  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.68/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.90  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.68/0.90  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.68/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.90  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.68/0.90  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.90  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.68/0.90  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.68/0.90  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.68/0.90  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.68/0.90  thf(d1_xboole_0, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.68/0.90  thf('0', plain,
% 0.68/0.90      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.68/0.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.90  thf(d5_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.68/0.90       ( ![D:$i]:
% 0.68/0.90         ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.90           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.68/0.90  thf('1', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X7 @ X6)
% 0.68/0.90          | (r2_hidden @ X7 @ X4)
% 0.68/0.90          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.68/0.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.90  thf('2', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.68/0.90         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.68/0.90      inference('simplify', [status(thm)], ['1'])).
% 0.68/0.90  thf(redefinition_k6_subset_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.68/0.90  thf('3', plain,
% 0.68/0.90      (![X17 : $i, X18 : $i]:
% 0.68/0.90         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.90  thf('4', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.68/0.90         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.68/0.90      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.90  thf('5', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((v1_xboole_0 @ (k6_subset_1 @ X1 @ X0))
% 0.68/0.90          | (r2_hidden @ (sk_B @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['0', '4'])).
% 0.68/0.90  thf('6', plain,
% 0.68/0.90      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.68/0.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.90  thf('7', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X7 @ X6)
% 0.68/0.90          | ~ (r2_hidden @ X7 @ X5)
% 0.68/0.90          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.68/0.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.90  thf('8', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X7 @ X5)
% 0.68/0.90          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.68/0.90      inference('simplify', [status(thm)], ['7'])).
% 0.68/0.90  thf('9', plain,
% 0.68/0.90      (![X17 : $i, X18 : $i]:
% 0.68/0.90         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.90  thf('10', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X7 @ X5)
% 0.68/0.90          | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.68/0.90      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.90  thf('11', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((v1_xboole_0 @ (k6_subset_1 @ X1 @ X0))
% 0.68/0.90          | ~ (r2_hidden @ (sk_B @ (k6_subset_1 @ X1 @ X0)) @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['6', '10'])).
% 0.68/0.90  thf('12', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))
% 0.68/0.90          | (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['5', '11'])).
% 0.68/0.90  thf('13', plain, (![X0 : $i]: (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['12'])).
% 0.68/0.90  thf(t3_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.68/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.68/0.90            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.68/0.90  thf('14', plain,
% 0.68/0.90      (![X9 : $i, X10 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X10))),
% 0.68/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.68/0.90  thf('15', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.90  thf('16', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.90  thf(t83_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.90  thf('17', plain,
% 0.68/0.90      (![X13 : $i, X14 : $i]:
% 0.68/0.90         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.68/0.90      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.68/0.90  thf('18', plain,
% 0.68/0.90      (![X17 : $i, X18 : $i]:
% 0.68/0.90         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.90  thf('19', plain,
% 0.68/0.90      (![X13 : $i, X14 : $i]:
% 0.68/0.90         (((k6_subset_1 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.68/0.90      inference('demod', [status(thm)], ['17', '18'])).
% 0.68/0.90  thf('20', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X0) | ((k6_subset_1 @ X1 @ X0) = (X1)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['16', '19'])).
% 0.68/0.90  thf(t29_yellow_6, conjecture,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.68/0.90             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.68/0.90           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.68/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.90    (~( ![A:$i]:
% 0.68/0.90        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.68/0.90          ( ![B:$i]:
% 0.68/0.90            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.68/0.90                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.68/0.90              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.68/0.90    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.68/0.90  thf('21', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(t10_waybel_0, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.68/0.90               ( ~( r1_waybel_0 @
% 0.68/0.90                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf('22', plain,
% 0.68/0.90      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.90         ((v2_struct_0 @ X28)
% 0.68/0.90          | ~ (l1_waybel_0 @ X28 @ X29)
% 0.68/0.90          | (r1_waybel_0 @ X29 @ X28 @ 
% 0.68/0.90             (k6_subset_1 @ (u1_struct_0 @ X29) @ X30))
% 0.68/0.90          | (r2_waybel_0 @ X29 @ X28 @ X30)
% 0.68/0.90          | ~ (l1_struct_0 @ X29)
% 0.68/0.90          | (v2_struct_0 @ X29))),
% 0.68/0.90      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.68/0.90  thf('23', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_A)
% 0.68/0.90          | ~ (l1_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.68/0.90          | (v2_struct_0 @ sk_B_2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['21', '22'])).
% 0.68/0.90  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('25', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.68/0.90          | (v2_struct_0 @ sk_B_2))),
% 0.68/0.90      inference('demod', [status(thm)], ['23', '24'])).
% 0.68/0.90  thf('26', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.68/0.90          | ~ (v1_xboole_0 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup+', [status(thm)], ['20', '25'])).
% 0.68/0.90  thf('27', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('28', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2)
% 0.68/0.90          | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['26', '27'])).
% 0.68/0.90  thf('29', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('30', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(d12_waybel_0, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.68/0.90           ( ![C:$i]:
% 0.68/0.90             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.68/0.90               ( ![D:$i]:
% 0.68/0.90                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.68/0.90                   ( ?[E:$i]:
% 0.68/0.90                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.68/0.90                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.68/0.90                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.68/0.90  thf('31', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         ((v2_struct_0 @ X22)
% 0.68/0.90          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.68/0.90          | (m1_subset_1 @ (sk_D_1 @ X24 @ X22 @ X23) @ (u1_struct_0 @ X22))
% 0.68/0.90          | (r2_waybel_0 @ X23 @ X22 @ X24)
% 0.68/0.90          | ~ (l1_struct_0 @ X23)
% 0.68/0.90          | (v2_struct_0 @ X23))),
% 0.68/0.90      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.68/0.90  thf('32', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_A)
% 0.68/0.90          | ~ (l1_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ 
% 0.68/0.90             (u1_struct_0 @ sk_B_2))
% 0.68/0.90          | (v2_struct_0 @ sk_B_2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['30', '31'])).
% 0.68/0.90  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('34', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ 
% 0.68/0.90             (u1_struct_0 @ sk_B_2))
% 0.68/0.90          | (v2_struct_0 @ sk_B_2))),
% 0.68/0.90      inference('demod', [status(thm)], ['32', '33'])).
% 0.68/0.90  thf('35', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X26 : $i, X27 : $i]:
% 0.68/0.90         ((v2_struct_0 @ X22)
% 0.68/0.90          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.68/0.90          | ~ (r2_waybel_0 @ X23 @ X22 @ X26)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ X23 @ X22 @ (sk_E @ X27 @ X26 @ X22 @ X23)) @ X26)
% 0.68/0.90          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X22))
% 0.68/0.90          | ~ (l1_struct_0 @ X23)
% 0.68/0.90          | (v2_struct_0 @ X23))),
% 0.68/0.90      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.68/0.90  thf('36', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (v2_struct_0 @ X1)
% 0.68/0.90          | ~ (l1_struct_0 @ X1)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X2 @ sk_B_2 @ X1)) @ 
% 0.68/0.90             X2)
% 0.68/0.90          | ~ (r2_waybel_0 @ X1 @ sk_B_2 @ X2)
% 0.68/0.90          | ~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['34', '35'])).
% 0.68/0.90  thf('37', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         (~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.68/0.90          | ~ (r2_waybel_0 @ X1 @ sk_B_2 @ X2)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X2 @ sk_B_2 @ X1)) @ 
% 0.68/0.90             X2)
% 0.68/0.90          | ~ (l1_struct_0 @ X1)
% 0.68/0.90          | (v2_struct_0 @ X1)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2))),
% 0.68/0.90      inference('simplify', [status(thm)], ['36'])).
% 0.68/0.90  thf('38', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | ~ (l1_struct_0 @ sk_A)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X1 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90             X1)
% 0.68/0.90          | ~ (r2_waybel_0 @ sk_A @ sk_B_2 @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['29', '37'])).
% 0.68/0.90  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('40', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X1 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90             X1)
% 0.68/0.90          | ~ (r2_waybel_0 @ sk_A @ sk_B_2 @ X1))),
% 0.68/0.90      inference('demod', [status(thm)], ['38', '39'])).
% 0.68/0.90  thf('41', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X1 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90             X1)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2))),
% 0.68/0.90      inference('simplify', [status(thm)], ['40'])).
% 0.68/0.90  thf('42', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_D_1 @ X1 @ sk_B_2 @ sk_A) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90             X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['28', '41'])).
% 0.68/0.90  thf('43', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((r2_hidden @ 
% 0.68/0.90           (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90            (sk_E @ (sk_D_1 @ X1 @ sk_B_2 @ sk_A) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90           X0)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2)
% 0.68/0.90          | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.90  thf('44', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.90  thf('45', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X0)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.68/0.90          | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['43', '44'])).
% 0.68/0.90  thf('46', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((r2_waybel_0 @ sk_A @ sk_B_2 @ X1)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (v2_struct_0 @ sk_B_2)
% 0.68/0.90          | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['45'])).
% 0.68/0.90  thf('47', plain,
% 0.68/0.90      (![X1 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['13', '46'])).
% 0.68/0.90  thf('48', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('49', plain,
% 0.68/0.90      (![X1 : $i]: ((r2_waybel_0 @ sk_A @ sk_B_2 @ X1) | (v2_struct_0 @ sk_A))),
% 0.68/0.90      inference('clc', [status(thm)], ['47', '48'])).
% 0.68/0.90  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('51', plain, (![X1 : $i]: (r2_waybel_0 @ sk_A @ sk_B_2 @ X1)),
% 0.68/0.90      inference('clc', [status(thm)], ['49', '50'])).
% 0.68/0.90  thf(existence_m1_subset_1, axiom,
% 0.68/0.90    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.68/0.90  thf('52', plain, (![X16 : $i]: (m1_subset_1 @ (sk_B_1 @ X16) @ X16)),
% 0.68/0.90      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.68/0.90  thf('53', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X26 : $i, X27 : $i]:
% 0.68/0.90         ((v2_struct_0 @ X22)
% 0.68/0.90          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.68/0.90          | ~ (r2_waybel_0 @ X23 @ X22 @ X26)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ X23 @ X22 @ (sk_E @ X27 @ X26 @ X22 @ X23)) @ X26)
% 0.68/0.90          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X22))
% 0.68/0.90          | ~ (l1_struct_0 @ X23)
% 0.68/0.90          | (v2_struct_0 @ X23))),
% 0.68/0.90      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.68/0.90  thf('54', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((v2_struct_0 @ X1)
% 0.68/0.90          | ~ (l1_struct_0 @ X1)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ X1 @ X0 @ 
% 0.68/0.90              (sk_E @ (sk_B_1 @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.68/0.90             X2)
% 0.68/0.90          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.68/0.90          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.68/0.90          | (v2_struct_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['52', '53'])).
% 0.68/0.90  thf('55', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B_2)
% 0.68/0.90          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90             X0)
% 0.68/0.90          | ~ (l1_struct_0 @ sk_A)
% 0.68/0.90          | (v2_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup-', [status(thm)], ['51', '54'])).
% 0.68/0.90  thf('56', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('58', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_B_2)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90             X0)
% 0.68/0.90          | (v2_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.68/0.90  thf('59', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('60', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((v2_struct_0 @ sk_A)
% 0.68/0.90          | (r2_hidden @ 
% 0.68/0.90             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90              (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90             X0))),
% 0.68/0.90      inference('clc', [status(thm)], ['58', '59'])).
% 0.68/0.90  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('62', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (r2_hidden @ 
% 0.68/0.90          (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.68/0.90           (sk_E @ (sk_B_1 @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A)) @ 
% 0.68/0.90          X0)),
% 0.68/0.90      inference('clc', [status(thm)], ['60', '61'])).
% 0.68/0.90  thf('63', plain, (![X0 : $i]: (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['12'])).
% 0.68/0.90  thf('64', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.68/0.90         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 0.68/0.90          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.68/0.90          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.68/0.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.90  thf('65', plain,
% 0.68/0.90      (![X17 : $i, X18 : $i]:
% 0.68/0.90         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.90  thf('66', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.68/0.90         (((X8) = (k6_subset_1 @ X4 @ X5))
% 0.68/0.90          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.68/0.90          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.68/0.90      inference('demod', [status(thm)], ['64', '65'])).
% 0.68/0.90  thf('67', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.68/0.90         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 0.68/0.90          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.68/0.90          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.68/0.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.90  thf('68', plain,
% 0.68/0.90      (![X17 : $i, X18 : $i]:
% 0.68/0.90         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.68/0.90  thf('69', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.68/0.90         (((X8) = (k6_subset_1 @ X4 @ X5))
% 0.68/0.90          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.68/0.90          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.68/0.90      inference('demod', [status(thm)], ['67', '68'])).
% 0.68/0.90  thf('70', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.68/0.90          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 0.68/0.90          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.68/0.90          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['66', '69'])).
% 0.68/0.90  thf('71', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (((X1) = (k6_subset_1 @ X0 @ X0))
% 0.68/0.90          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.68/0.90      inference('simplify', [status(thm)], ['70'])).
% 0.68/0.90  thf('72', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.90  thf('73', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (((X0) = (k6_subset_1 @ X1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['71', '72'])).
% 0.68/0.90  thf('74', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['63', '73'])).
% 0.68/0.90  thf('75', plain,
% 0.68/0.90      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X7 @ X5)
% 0.68/0.90          | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.68/0.90      inference('demod', [status(thm)], ['8', '9'])).
% 0.68/0.90  thf('76', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X0))
% 0.68/0.90          | ~ (r2_hidden @ X2 @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['74', '75'])).
% 0.68/0.90  thf('77', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.68/0.90      inference('condensation', [status(thm)], ['76'])).
% 0.68/0.90  thf('78', plain, ($false), inference('sup-', [status(thm)], ['62', '77'])).
% 0.68/0.90  
% 0.68/0.90  % SZS output end Refutation
% 0.68/0.90  
% 0.68/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
