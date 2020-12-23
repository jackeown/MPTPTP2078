%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PV0lxEvrl2

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:59 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 208 expanded)
%              Number of leaves         :   34 (  76 expanded)
%              Depth                    :   21
%              Number of atoms          :  919 (2319 expanded)
%              Number of equality atoms :   20 (  43 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
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

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ( r1_waybel_0 @ X23 @ X22 @ ( k6_subset_1 @ ( u1_struct_0 @ X23 ) @ X24 ) )
      | ( r2_waybel_0 @ X23 @ X22 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( r1_tarski @ C @ D )
             => ( ( ( r1_waybel_0 @ A @ B @ C )
                 => ( r1_waybel_0 @ A @ B @ D ) )
                & ( ( r2_waybel_0 @ A @ B @ C )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ~ ( r1_waybel_0 @ X27 @ X26 @ X28 )
      | ( r1_waybel_0 @ X27 @ X26 @ X29 )
      | ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('28',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( sk_B @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

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

thf('29',plain,(
    ! [X16: $i,X17: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_0 @ X17 @ X16 @ X20 )
      | ( m1_subset_1 @ ( sk_E @ X21 @ X20 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_0 @ X17 @ X16 @ X20 )
      | ( r2_hidden @ ( k2_waybel_0 @ X17 @ X16 @ ( sk_E @ X21 @ X20 @ X16 @ X17 ) ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( sk_B @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k1_zfmisc_1 @ X0 ) )
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k1_zfmisc_1 @ X0 ) )
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k6_subset_1 @ X0 @ X0 )
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k6_subset_1 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference('sup-',[status(thm)],['48','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PV0lxEvrl2
% 0.07/0.27  % Computer   : n012.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 16:49:22 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  % Running portfolio for 600 s
% 0.07/0.27  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.07/0.27  % Number of cores: 8
% 0.07/0.28  % Python version: Python 3.6.8
% 0.07/0.28  % Running in FO mode
% 0.63/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.83  % Solved by: fo/fo7.sh
% 0.63/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.83  % done 651 iterations in 0.444s
% 0.63/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.83  % SZS output start Refutation
% 0.63/0.83  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.63/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.63/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.83  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.63/0.83  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.63/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.63/0.83  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.63/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.63/0.83  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.63/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.63/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.63/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.63/0.83  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.63/0.83  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.63/0.83  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.63/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.63/0.83  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.63/0.83  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.63/0.83  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.63/0.83  thf(d3_tarski, axiom,
% 0.63/0.83    (![A:$i,B:$i]:
% 0.63/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.63/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.63/0.83  thf('0', plain,
% 0.63/0.83      (![X1 : $i, X3 : $i]:
% 0.63/0.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.63/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.63/0.83  thf(d5_xboole_0, axiom,
% 0.63/0.83    (![A:$i,B:$i,C:$i]:
% 0.63/0.83     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.63/0.83       ( ![D:$i]:
% 0.63/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.63/0.83           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.63/0.83  thf('1', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.63/0.83         (~ (r2_hidden @ X8 @ X7)
% 0.63/0.83          | (r2_hidden @ X8 @ X5)
% 0.63/0.83          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.63/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.63/0.83  thf('2', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.63/0.83         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.63/0.83      inference('simplify', [status(thm)], ['1'])).
% 0.63/0.83  thf(redefinition_k6_subset_1, axiom,
% 0.63/0.83    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.63/0.83  thf('3', plain,
% 0.63/0.83      (![X11 : $i, X12 : $i]:
% 0.63/0.83         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.63/0.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.83  thf('4', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.63/0.83         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 0.63/0.83      inference('demod', [status(thm)], ['2', '3'])).
% 0.63/0.83  thf('5', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.83         ((r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X2)
% 0.63/0.83          | (r2_hidden @ (sk_C @ X2 @ (k6_subset_1 @ X1 @ X0)) @ X1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['0', '4'])).
% 0.63/0.83  thf('6', plain,
% 0.63/0.83      (![X1 : $i, X3 : $i]:
% 0.63/0.83         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.63/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.63/0.83  thf('7', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)
% 0.63/0.83          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.63/0.83  thf('8', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.63/0.83      inference('simplify', [status(thm)], ['7'])).
% 0.63/0.83  thf(t29_yellow_6, conjecture,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.63/0.83             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.63/0.83           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.63/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.83    (~( ![A:$i]:
% 0.63/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.63/0.83          ( ![B:$i]:
% 0.63/0.83            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.63/0.83                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.63/0.83              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.63/0.83    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.63/0.83  thf('9', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf(t10_waybel_0, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.63/0.83           ( ![C:$i]:
% 0.63/0.83             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.63/0.83               ( ~( r1_waybel_0 @
% 0.63/0.83                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.63/0.83  thf('10', plain,
% 0.63/0.83      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.63/0.83         ((v2_struct_0 @ X22)
% 0.63/0.83          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.63/0.83          | (r1_waybel_0 @ X23 @ X22 @ 
% 0.63/0.83             (k6_subset_1 @ (u1_struct_0 @ X23) @ X24))
% 0.63/0.83          | (r2_waybel_0 @ X23 @ X22 @ X24)
% 0.63/0.83          | ~ (l1_struct_0 @ X23)
% 0.63/0.83          | (v2_struct_0 @ X23))),
% 0.63/0.83      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.63/0.83  thf('11', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_A)
% 0.63/0.83          | ~ (l1_struct_0 @ sk_A)
% 0.63/0.83          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.63/0.83          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.63/0.83             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.63/0.83          | (v2_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.63/0.83  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('13', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_A)
% 0.63/0.83          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.63/0.83          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.63/0.83             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.63/0.83          | (v2_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('demod', [status(thm)], ['11', '12'])).
% 0.63/0.83  thf(t8_waybel_0, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.63/0.83           ( ![C:$i,D:$i]:
% 0.63/0.83             ( ( r1_tarski @ C @ D ) =>
% 0.63/0.83               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 0.63/0.83                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.63/0.83  thf('14', plain,
% 0.63/0.83      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.63/0.83         ((v2_struct_0 @ X26)
% 0.63/0.83          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.63/0.83          | ~ (r1_waybel_0 @ X27 @ X26 @ X28)
% 0.63/0.83          | (r1_waybel_0 @ X27 @ X26 @ X29)
% 0.63/0.83          | ~ (r1_tarski @ X28 @ X29)
% 0.63/0.83          | ~ (l1_struct_0 @ X27)
% 0.63/0.83          | (v2_struct_0 @ X27))),
% 0.63/0.83      inference('cnf', [status(esa)], [t8_waybel_0])).
% 0.63/0.83  thf('15', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1)
% 0.63/0.83          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.63/0.83          | (v2_struct_0 @ sk_A)
% 0.63/0.83          | (v2_struct_0 @ sk_A)
% 0.63/0.83          | ~ (l1_struct_0 @ sk_A)
% 0.63/0.83          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.63/0.83          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.63/0.83          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.63/0.83          | (v2_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.63/0.83  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('17', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('18', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1)
% 0.63/0.83          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.63/0.83          | (v2_struct_0 @ sk_A)
% 0.63/0.83          | (v2_struct_0 @ sk_A)
% 0.63/0.83          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.63/0.83          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.63/0.83          | (v2_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.63/0.83  thf('19', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((r1_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.63/0.83          | ~ (r1_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ X1)
% 0.63/0.83          | (v2_struct_0 @ sk_A)
% 0.63/0.83          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.63/0.83          | (v2_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('simplify', [status(thm)], ['18'])).
% 0.63/0.83  thf('20', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1)
% 0.63/0.83          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.63/0.83          | (v2_struct_0 @ sk_A)
% 0.63/0.83          | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.83      inference('sup-', [status(thm)], ['8', '19'])).
% 0.63/0.83  thf('21', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('22', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_A)
% 0.63/0.83          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.63/0.83          | (v2_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.63/0.83  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('24', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.63/0.83      inference('clc', [status(thm)], ['22', '23'])).
% 0.63/0.83  thf('25', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('26', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.63/0.83      inference('clc', [status(thm)], ['24', '25'])).
% 0.63/0.83  thf('27', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.63/0.83      inference('clc', [status(thm)], ['24', '25'])).
% 0.63/0.83  thf(existence_m1_subset_1, axiom,
% 0.63/0.83    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.63/0.83  thf('28', plain, (![X10 : $i]: (m1_subset_1 @ (sk_B @ X10) @ X10)),
% 0.63/0.83      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.63/0.83  thf(d12_waybel_0, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.63/0.83           ( ![C:$i]:
% 0.63/0.83             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.63/0.83               ( ![D:$i]:
% 0.63/0.83                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.63/0.83                   ( ?[E:$i]:
% 0.63/0.83                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.63/0.83                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.63/0.83                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.63/0.83  thf('29', plain,
% 0.63/0.83      (![X16 : $i, X17 : $i, X20 : $i, X21 : $i]:
% 0.63/0.83         ((v2_struct_0 @ X16)
% 0.63/0.83          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.63/0.83          | ~ (r2_waybel_0 @ X17 @ X16 @ X20)
% 0.63/0.83          | (m1_subset_1 @ (sk_E @ X21 @ X20 @ X16 @ X17) @ (u1_struct_0 @ X16))
% 0.63/0.83          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X16))
% 0.63/0.83          | ~ (l1_struct_0 @ X17)
% 0.63/0.83          | (v2_struct_0 @ X17))),
% 0.63/0.83      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.63/0.83  thf('30', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.83         ((v2_struct_0 @ X1)
% 0.63/0.83          | ~ (l1_struct_0 @ X1)
% 0.63/0.83          | (m1_subset_1 @ 
% 0.63/0.83             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.63/0.83             (u1_struct_0 @ X0))
% 0.63/0.83          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.63/0.83          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.63/0.83          | (v2_struct_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['28', '29'])).
% 0.63/0.83  thf('31', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1)
% 0.63/0.83          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.63/0.83          | (m1_subset_1 @ 
% 0.63/0.83             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83             (u1_struct_0 @ sk_B_1))
% 0.63/0.83          | ~ (l1_struct_0 @ sk_A)
% 0.63/0.83          | (v2_struct_0 @ sk_A))),
% 0.63/0.83      inference('sup-', [status(thm)], ['27', '30'])).
% 0.63/0.83  thf('32', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('34', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1)
% 0.63/0.83          | (m1_subset_1 @ 
% 0.63/0.83             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83             (u1_struct_0 @ sk_B_1))
% 0.63/0.83          | (v2_struct_0 @ sk_A))),
% 0.63/0.83      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.63/0.83  thf('35', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('36', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_A)
% 0.63/0.83          | (m1_subset_1 @ 
% 0.63/0.83             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83             (u1_struct_0 @ sk_B_1)))),
% 0.63/0.83      inference('clc', [status(thm)], ['34', '35'])).
% 0.63/0.83  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('38', plain,
% 0.63/0.83      (![X0 : $i]:
% 0.63/0.83         (m1_subset_1 @ 
% 0.63/0.83          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83          (u1_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('clc', [status(thm)], ['36', '37'])).
% 0.63/0.83  thf('39', plain,
% 0.63/0.83      (![X16 : $i, X17 : $i, X20 : $i, X21 : $i]:
% 0.63/0.83         ((v2_struct_0 @ X16)
% 0.63/0.83          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.63/0.83          | ~ (r2_waybel_0 @ X17 @ X16 @ X20)
% 0.63/0.83          | (r2_hidden @ 
% 0.63/0.83             (k2_waybel_0 @ X17 @ X16 @ (sk_E @ X21 @ X20 @ X16 @ X17)) @ X20)
% 0.63/0.83          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X16))
% 0.63/0.83          | ~ (l1_struct_0 @ X17)
% 0.63/0.83          | (v2_struct_0 @ X17))),
% 0.63/0.83      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.63/0.83  thf('40', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.83         ((v2_struct_0 @ X1)
% 0.63/0.83          | ~ (l1_struct_0 @ X1)
% 0.63/0.83          | (r2_hidden @ 
% 0.63/0.83             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.63/0.83              (sk_E @ 
% 0.63/0.83               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83               X2 @ sk_B_1 @ X1)) @ 
% 0.63/0.83             X2)
% 0.63/0.83          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.63/0.83          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.63/0.83          | (v2_struct_0 @ sk_B_1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.63/0.83  thf('41', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1)
% 0.63/0.83          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.63/0.83          | (r2_hidden @ 
% 0.63/0.83             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.63/0.83              (sk_E @ 
% 0.63/0.83               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83               X0 @ sk_B_1 @ sk_A)) @ 
% 0.63/0.83             X0)
% 0.63/0.83          | ~ (l1_struct_0 @ sk_A)
% 0.63/0.83          | (v2_struct_0 @ sk_A))),
% 0.63/0.83      inference('sup-', [status(thm)], ['26', '40'])).
% 0.63/0.83  thf('42', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('44', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_B_1)
% 0.63/0.83          | (r2_hidden @ 
% 0.63/0.83             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.63/0.83              (sk_E @ 
% 0.63/0.83               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83               X0 @ sk_B_1 @ sk_A)) @ 
% 0.63/0.83             X0)
% 0.63/0.83          | (v2_struct_0 @ sk_A))),
% 0.63/0.83      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.63/0.83  thf('45', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('46', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((v2_struct_0 @ sk_A)
% 0.63/0.83          | (r2_hidden @ 
% 0.63/0.83             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.63/0.83              (sk_E @ 
% 0.63/0.83               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83               X0 @ sk_B_1 @ sk_A)) @ 
% 0.63/0.83             X0))),
% 0.63/0.83      inference('clc', [status(thm)], ['44', '45'])).
% 0.63/0.83  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('48', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         (r2_hidden @ 
% 0.63/0.83          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.63/0.83           (sk_E @ 
% 0.63/0.83            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.63/0.83            X0 @ sk_B_1 @ sk_A)) @ 
% 0.63/0.83          X0)),
% 0.63/0.83      inference('clc', [status(thm)], ['46', '47'])).
% 0.63/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.63/0.83  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.63/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.63/0.83  thf('50', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.63/0.83         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.63/0.83          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.63/0.83          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.63/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.63/0.83  thf('51', plain,
% 0.63/0.83      (![X11 : $i, X12 : $i]:
% 0.63/0.83         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.63/0.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.83  thf('52', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.63/0.83         (((X9) = (k6_subset_1 @ X5 @ X6))
% 0.63/0.83          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.63/0.83          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.63/0.83      inference('demod', [status(thm)], ['50', '51'])).
% 0.63/0.83  thf('53', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.63/0.83         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.63/0.83          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.63/0.83          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.63/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.63/0.83  thf('54', plain,
% 0.63/0.83      (![X11 : $i, X12 : $i]:
% 0.63/0.83         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.63/0.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.83  thf('55', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.63/0.83         (((X9) = (k6_subset_1 @ X5 @ X6))
% 0.63/0.83          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.63/0.83          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.63/0.83      inference('demod', [status(thm)], ['53', '54'])).
% 0.63/0.83  thf('56', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.63/0.83          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 0.63/0.83          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.63/0.83          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 0.63/0.83      inference('sup-', [status(thm)], ['52', '55'])).
% 0.63/0.83  thf('57', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         (((X1) = (k6_subset_1 @ X0 @ X0))
% 0.63/0.83          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.63/0.83      inference('simplify', [status(thm)], ['56'])).
% 0.63/0.83  thf('58', plain, (![X10 : $i]: (m1_subset_1 @ (sk_B @ X10) @ X10)),
% 0.63/0.83      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.63/0.83  thf(t5_subset, axiom,
% 0.63/0.83    (![A:$i,B:$i,C:$i]:
% 0.63/0.83     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.63/0.83          ( v1_xboole_0 @ C ) ) ))).
% 0.63/0.83  thf('59', plain,
% 0.63/0.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.83         (~ (r2_hidden @ X13 @ X14)
% 0.63/0.83          | ~ (v1_xboole_0 @ X15)
% 0.63/0.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.63/0.83      inference('cnf', [status(esa)], [t5_subset])).
% 0.63/0.83  thf('60', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         (~ (v1_xboole_0 @ X0)
% 0.63/0.83          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 0.63/0.83      inference('sup-', [status(thm)], ['58', '59'])).
% 0.63/0.83  thf('61', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         (((sk_B @ (k1_zfmisc_1 @ X0)) = (k6_subset_1 @ X1 @ X1))
% 0.63/0.83          | ~ (v1_xboole_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['57', '60'])).
% 0.63/0.83  thf('62', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         (((sk_B @ (k1_zfmisc_1 @ X0)) = (k6_subset_1 @ X1 @ X1))
% 0.63/0.83          | ~ (v1_xboole_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['57', '60'])).
% 0.63/0.83  thf('63', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.83         (((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))
% 0.63/0.83          | ~ (v1_xboole_0 @ X2)
% 0.63/0.83          | ~ (v1_xboole_0 @ X2))),
% 0.63/0.83      inference('sup+', [status(thm)], ['61', '62'])).
% 0.63/0.83  thf('64', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.83         (~ (v1_xboole_0 @ X2)
% 0.63/0.83          | ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1)))),
% 0.63/0.83      inference('simplify', [status(thm)], ['63'])).
% 0.63/0.83  thf('65', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ X1 @ X1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['49', '64'])).
% 0.63/0.83  thf('66', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.63/0.83         (~ (r2_hidden @ X8 @ X7)
% 0.63/0.83          | ~ (r2_hidden @ X8 @ X6)
% 0.63/0.83          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.63/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.63/0.83  thf('67', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.63/0.83         (~ (r2_hidden @ X8 @ X6)
% 0.63/0.83          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.63/0.83      inference('simplify', [status(thm)], ['66'])).
% 0.63/0.83  thf('68', plain,
% 0.63/0.83      (![X11 : $i, X12 : $i]:
% 0.63/0.83         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.63/0.83      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.83  thf('69', plain,
% 0.63/0.83      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.63/0.83         (~ (r2_hidden @ X8 @ X6)
% 0.63/0.83          | ~ (r2_hidden @ X8 @ (k6_subset_1 @ X5 @ X6)))),
% 0.63/0.83      inference('demod', [status(thm)], ['67', '68'])).
% 0.63/0.83  thf('70', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.83         (~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X0))
% 0.63/0.83          | ~ (r2_hidden @ X2 @ X1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['65', '69'])).
% 0.63/0.83  thf('71', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.63/0.83      inference('condensation', [status(thm)], ['70'])).
% 0.63/0.83  thf('72', plain, ($false), inference('sup-', [status(thm)], ['48', '71'])).
% 0.63/0.83  
% 0.63/0.83  % SZS output end Refutation
% 0.63/0.83  
% 0.63/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
