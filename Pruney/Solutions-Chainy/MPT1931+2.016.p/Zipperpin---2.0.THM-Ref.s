%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kyst1k3FXq

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:58 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 185 expanded)
%              Number of leaves         :   37 (  71 expanded)
%              Depth                    :   24
%              Number of atoms          :  708 (1561 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k6_subset_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k6_subset_1 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','33'])).

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

thf('35',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ~ ( r2_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X33 )
      | ( r2_waybel_0 @ X33 @ X32 @ ( k6_subset_1 @ ( u1_struct_0 @ X33 ) @ X34 ) )
      | ( r1_waybel_0 @ X33 @ X32 @ X34 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

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

thf('50',plain,(
    ! [X24: $i,X25: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( r2_waybel_0 @ X25 @ X24 @ X28 )
      | ( r2_hidden @ ( k2_waybel_0 @ X25 @ X24 @ ( sk_E @ X29 @ X28 @ X24 @ X25 ) ) @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['27'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['59','60'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('68',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_waybel_0 @ X30 @ X31 )
      | ( l1_orders_2 @ X30 )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('69',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['66','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kyst1k3FXq
% 0.17/0.38  % Computer   : n007.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 18:28:51 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.91/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.13  % Solved by: fo/fo7.sh
% 0.91/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.13  % done 1049 iterations in 0.658s
% 0.91/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.13  % SZS output start Refutation
% 0.91/1.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.13  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.91/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.13  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.13  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.91/1.13  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.13  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.91/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.13  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.91/1.13  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.91/1.13  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.91/1.13  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.91/1.13  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.91/1.13  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.91/1.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.91/1.13  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.91/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.13  thf(dt_l1_orders_2, axiom,
% 0.91/1.13    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.91/1.13  thf('0', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_orders_2 @ X23))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.91/1.13  thf(d1_xboole_0, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.13  thf('1', plain,
% 0.91/1.13      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.91/1.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.13  thf(d5_xboole_0, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.91/1.13       ( ![D:$i]:
% 0.91/1.13         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.13           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.91/1.13  thf('2', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X7 @ X6)
% 0.91/1.13          | (r2_hidden @ X7 @ X4)
% 0.91/1.13          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.13  thf('3', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.91/1.13         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['2'])).
% 0.91/1.13  thf(redefinition_k6_subset_1, axiom,
% 0.91/1.13    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.91/1.13  thf('4', plain,
% 0.91/1.13      (![X9 : $i, X10 : $i]:
% 0.91/1.13         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.91/1.13      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.13  thf('5', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.91/1.13         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.91/1.13      inference('demod', [status(thm)], ['3', '4'])).
% 0.91/1.13  thf('6', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((v1_xboole_0 @ (k6_subset_1 @ X1 @ X0))
% 0.91/1.13          | (r2_hidden @ (sk_B @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['1', '5'])).
% 0.91/1.13  thf('7', plain,
% 0.91/1.13      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.91/1.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.13  thf('8', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X7 @ X6)
% 0.91/1.13          | ~ (r2_hidden @ X7 @ X5)
% 0.91/1.13          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.13  thf('9', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X7 @ X5)
% 0.91/1.13          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['8'])).
% 0.91/1.13  thf('10', plain,
% 0.91/1.13      (![X9 : $i, X10 : $i]:
% 0.91/1.13         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.91/1.13      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.13  thf('11', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X7 @ X5)
% 0.91/1.13          | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.91/1.13      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.13  thf('12', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((v1_xboole_0 @ (k6_subset_1 @ X1 @ X0))
% 0.91/1.13          | ~ (r2_hidden @ (sk_B @ (k6_subset_1 @ X1 @ X0)) @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['7', '11'])).
% 0.91/1.13  thf('13', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ((v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))
% 0.91/1.13          | (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['6', '12'])).
% 0.91/1.13  thf('14', plain, (![X0 : $i]: (v1_xboole_0 @ (k6_subset_1 @ X0 @ X0))),
% 0.91/1.13      inference('simplify', [status(thm)], ['13'])).
% 0.91/1.13  thf('15', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.91/1.13         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 0.91/1.13          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.91/1.13          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.13  thf('16', plain,
% 0.91/1.13      (![X9 : $i, X10 : $i]:
% 0.91/1.13         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.91/1.13      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.91/1.13  thf('17', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.91/1.13         (((X8) = (k6_subset_1 @ X4 @ X5))
% 0.91/1.13          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.91/1.13          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.91/1.13      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.13  thf(t4_subset_1, axiom,
% 0.91/1.13    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.13  thf('18', plain,
% 0.91/1.13      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.91/1.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.13  thf(t3_subset, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.13  thf('19', plain,
% 0.91/1.13      (![X14 : $i, X15 : $i]:
% 0.91/1.13         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.13  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.13      inference('sup-', [status(thm)], ['18', '19'])).
% 0.91/1.13  thf('21', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.91/1.13         (((X8) = (k6_subset_1 @ X4 @ X5))
% 0.91/1.13          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 0.91/1.13          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.91/1.13      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.13  thf('22', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.13          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.91/1.13      inference('eq_fact', [status(thm)], ['21'])).
% 0.91/1.13  thf(t7_ordinal1, axiom,
% 0.91/1.13    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.13  thf('23', plain,
% 0.91/1.13      (![X20 : $i, X21 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.91/1.13      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.91/1.13  thf('24', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (((X0) = (k6_subset_1 @ X0 @ X1))
% 0.91/1.13          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X1 @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.13  thf('25', plain,
% 0.91/1.13      (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['20', '24'])).
% 0.91/1.13  thf('26', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X7 @ X5)
% 0.91/1.13          | ~ (r2_hidden @ X7 @ (k6_subset_1 @ X4 @ X5)))),
% 0.91/1.13      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.13  thf('27', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.13  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.91/1.13      inference('condensation', [status(thm)], ['27'])).
% 0.91/1.13  thf('29', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.91/1.13          | ((X1) = (k6_subset_1 @ k1_xboole_0 @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['17', '28'])).
% 0.91/1.13  thf('30', plain,
% 0.91/1.13      (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['20', '24'])).
% 0.91/1.13  thf('31', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.91/1.13          | ((X1) = (k1_xboole_0)))),
% 0.91/1.13      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.13  thf('32', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.13  thf('33', plain,
% 0.91/1.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.13  thf('34', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['14', '33'])).
% 0.91/1.13  thf(t29_yellow_6, conjecture,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.91/1.13             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.91/1.13           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.13    (~( ![A:$i]:
% 0.91/1.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.13          ( ![B:$i]:
% 0.91/1.13            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.91/1.13                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.91/1.13              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.91/1.13    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.91/1.13  thf('35', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(t9_waybel_0, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.91/1.13               ( ~( r2_waybel_0 @
% 0.91/1.13                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf('36', plain,
% 0.91/1.13      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.91/1.13         ((v2_struct_0 @ X32)
% 0.91/1.13          | ~ (l1_waybel_0 @ X32 @ X33)
% 0.91/1.13          | (r2_waybel_0 @ X33 @ X32 @ 
% 0.91/1.13             (k6_subset_1 @ (u1_struct_0 @ X33) @ X34))
% 0.91/1.13          | (r1_waybel_0 @ X33 @ X32 @ X34)
% 0.91/1.13          | ~ (l1_struct_0 @ X33)
% 0.91/1.13          | (v2_struct_0 @ X33))),
% 0.91/1.13      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.91/1.13  thf('37', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ((v2_struct_0 @ sk_A)
% 0.91/1.13          | ~ (l1_struct_0 @ sk_A)
% 0.91/1.13          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.91/1.13          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.91/1.13             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.91/1.13          | (v2_struct_0 @ sk_B_1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.13  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('39', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ((v2_struct_0 @ sk_A)
% 0.91/1.13          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.91/1.13          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.91/1.13             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.91/1.13          | (v2_struct_0 @ sk_B_1))),
% 0.91/1.13      inference('demod', [status(thm)], ['37', '38'])).
% 0.91/1.13  thf('40', plain,
% 0.91/1.13      (((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.91/1.13        | (v2_struct_0 @ sk_B_1)
% 0.91/1.13        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.91/1.13        | (v2_struct_0 @ sk_A))),
% 0.91/1.13      inference('sup+', [status(thm)], ['34', '39'])).
% 0.91/1.13  thf('41', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('42', plain,
% 0.91/1.13      (((v2_struct_0 @ sk_A)
% 0.91/1.13        | (v2_struct_0 @ sk_B_1)
% 0.91/1.13        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.13  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('44', plain,
% 0.91/1.13      (((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0) | (v2_struct_0 @ sk_B_1))),
% 0.91/1.13      inference('clc', [status(thm)], ['42', '43'])).
% 0.91/1.13  thf('45', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('46', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.91/1.13      inference('clc', [status(thm)], ['44', '45'])).
% 0.91/1.13  thf('47', plain,
% 0.91/1.13      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.91/1.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.13  thf(t1_subset, axiom,
% 0.91/1.13    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.91/1.13  thf('48', plain,
% 0.91/1.13      (![X12 : $i, X13 : $i]:
% 0.91/1.13         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.91/1.13      inference('cnf', [status(esa)], [t1_subset])).
% 0.91/1.13  thf('49', plain,
% 0.91/1.13      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['47', '48'])).
% 0.91/1.13  thf(d12_waybel_0, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.13       ( ![B:$i]:
% 0.91/1.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.91/1.13           ( ![C:$i]:
% 0.91/1.13             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.91/1.13               ( ![D:$i]:
% 0.91/1.13                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.91/1.13                   ( ?[E:$i]:
% 0.91/1.13                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.91/1.13                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.91/1.13                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.13  thf('50', plain,
% 0.91/1.13      (![X24 : $i, X25 : $i, X28 : $i, X29 : $i]:
% 0.91/1.13         ((v2_struct_0 @ X24)
% 0.91/1.13          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.91/1.13          | ~ (r2_waybel_0 @ X25 @ X24 @ X28)
% 0.91/1.13          | (r2_hidden @ 
% 0.91/1.13             (k2_waybel_0 @ X25 @ X24 @ (sk_E @ X29 @ X28 @ X24 @ X25)) @ X28)
% 0.91/1.13          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X24))
% 0.91/1.13          | ~ (l1_struct_0 @ X25)
% 0.91/1.13          | (v2_struct_0 @ X25))),
% 0.91/1.13      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.91/1.13  thf('51', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.91/1.13          | (v2_struct_0 @ X1)
% 0.91/1.13          | ~ (l1_struct_0 @ X1)
% 0.91/1.13          | (r2_hidden @ 
% 0.91/1.13             (k2_waybel_0 @ X1 @ X0 @ 
% 0.91/1.13              (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.91/1.13             X2)
% 0.91/1.13          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.91/1.13          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.91/1.13          | (v2_struct_0 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.13  thf('52', plain,
% 0.91/1.13      (((v2_struct_0 @ sk_B_1)
% 0.91/1.13        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.91/1.13        | (r2_hidden @ 
% 0.91/1.13           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.91/1.13            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.91/1.13             sk_A)) @ 
% 0.91/1.13           k1_xboole_0)
% 0.91/1.13        | ~ (l1_struct_0 @ sk_A)
% 0.91/1.13        | (v2_struct_0 @ sk_A)
% 0.91/1.13        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['46', '51'])).
% 0.91/1.13  thf('53', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('55', plain,
% 0.91/1.13      (((v2_struct_0 @ sk_B_1)
% 0.91/1.13        | (r2_hidden @ 
% 0.91/1.13           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.91/1.13            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.91/1.13             sk_A)) @ 
% 0.91/1.13           k1_xboole_0)
% 0.91/1.13        | (v2_struct_0 @ sk_A)
% 0.91/1.13        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.91/1.13      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.91/1.13  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.91/1.13      inference('condensation', [status(thm)], ['27'])).
% 0.91/1.13  thf('57', plain,
% 0.91/1.13      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.91/1.13        | (v2_struct_0 @ sk_A)
% 0.91/1.13        | (v2_struct_0 @ sk_B_1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['55', '56'])).
% 0.91/1.13  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('59', plain,
% 0.91/1.13      (((v2_struct_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.91/1.13      inference('clc', [status(thm)], ['57', '58'])).
% 0.91/1.13  thf('60', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('61', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.91/1.13      inference('clc', [status(thm)], ['59', '60'])).
% 0.91/1.13  thf(fc2_struct_0, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.13       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.13  thf('62', plain,
% 0.91/1.13      (![X22 : $i]:
% 0.91/1.13         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.91/1.13          | ~ (l1_struct_0 @ X22)
% 0.91/1.13          | (v2_struct_0 @ X22))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.91/1.13  thf('63', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['61', '62'])).
% 0.91/1.13  thf('64', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('65', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.91/1.13      inference('clc', [status(thm)], ['63', '64'])).
% 0.91/1.13  thf('66', plain, (~ (l1_orders_2 @ sk_B_1)),
% 0.91/1.13      inference('sup-', [status(thm)], ['0', '65'])).
% 0.91/1.13  thf('67', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(dt_l1_waybel_0, axiom,
% 0.91/1.13    (![A:$i]:
% 0.91/1.13     ( ( l1_struct_0 @ A ) =>
% 0.91/1.13       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.91/1.13  thf('68', plain,
% 0.91/1.13      (![X30 : $i, X31 : $i]:
% 0.91/1.13         (~ (l1_waybel_0 @ X30 @ X31)
% 0.91/1.13          | (l1_orders_2 @ X30)
% 0.91/1.13          | ~ (l1_struct_0 @ X31))),
% 0.91/1.13      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.91/1.13  thf('69', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['67', '68'])).
% 0.91/1.13  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('71', plain, ((l1_orders_2 @ sk_B_1)),
% 0.91/1.13      inference('demod', [status(thm)], ['69', '70'])).
% 0.91/1.13  thf('72', plain, ($false), inference('demod', [status(thm)], ['66', '71'])).
% 0.91/1.13  
% 0.91/1.13  % SZS output end Refutation
% 0.91/1.13  
% 0.99/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
