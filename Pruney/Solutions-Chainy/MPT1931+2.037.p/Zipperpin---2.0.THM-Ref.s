%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IjCQe6PEp5

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:01 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 354 expanded)
%              Number of leaves         :   32 ( 116 expanded)
%              Depth                    :   26
%              Number of atoms          : 1012 (3953 expanded)
%              Number of equality atoms :   19 ( 114 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k6_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

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

thf('23',plain,(
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

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ( r2_waybel_0 @ X25 @ X24 @ ( k6_subset_1 @ ( u1_struct_0 @ X25 ) @ X26 ) )
      | ( r1_waybel_0 @ X25 @ X24 @ X26 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t9_waybel_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
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

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( m1_subset_1 @ ( sk_D_1 @ X20 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r2_waybel_0 @ X19 @ X18 @ X20 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( r2_waybel_0 @ X19 @ X18 @ X22 )
      | ( r2_hidden @ ( k2_waybel_0 @ X19 @ X18 @ ( sk_E @ X23 @ X22 @ X18 @ X19 ) ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_waybel_0 @ sk_A @ sk_B_1 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X1 @ sk_B_1 @ sk_A ) ) @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['20'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('56',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( r2_waybel_0 @ X19 @ X18 @ X22 )
      | ( m1_subset_1 @ ( sk_E @ X23 @ X22 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X18: $i,X19: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( r2_waybel_0 @ X19 @ X18 @ X22 )
      | ( r2_hidden @ ( k2_waybel_0 @ X19 @ X18 @ ( sk_E @ X23 @ X22 @ X18 @ X19 ) ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['20'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('sup-',[status(thm)],['76','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IjCQe6PEp5
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 404 iterations in 0.234s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.69  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.51/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.69  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.51/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.69  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.51/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.69  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.51/0.69  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.51/0.69  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.51/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.51/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.69  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.51/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.69  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.51/0.69  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.51/0.69  thf(d5_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.51/0.69       ( ![D:$i]:
% 0.51/0.69         ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.69           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.51/0.69  thf('0', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.51/0.69         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.51/0.69  thf(redefinition_k6_subset_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.51/0.69  thf('2', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.51/0.69         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.51/0.69         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.51/0.69          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.51/0.69  thf('4', plain,
% 0.51/0.69      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.51/0.69  thf('5', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.51/0.69         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.51/0.69          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('6', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.51/0.69          | ((X1) = (k6_subset_1 @ X0 @ X0))
% 0.51/0.69          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.51/0.69          | ((X1) = (k6_subset_1 @ X0 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['2', '5'])).
% 0.51/0.69  thf('7', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (((X1) = (k6_subset_1 @ X0 @ X0))
% 0.51/0.69          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.51/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.51/0.69  thf(t4_subset_1, axiom,
% 0.51/0.69    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.51/0.69  thf('8', plain,
% 0.51/0.69      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.51/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.51/0.69  thf(t3_subset, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.69  thf('9', plain,
% 0.51/0.69      (![X10 : $i, X11 : $i]:
% 0.51/0.69         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.69  thf('10', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.51/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.69  thf('11', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.51/0.69         (((X5) = (k6_subset_1 @ X1 @ X2))
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.51/0.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('12', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.51/0.69          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.51/0.69      inference('eq_fact', [status(thm)], ['11'])).
% 0.51/0.69  thf(t7_ordinal1, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      (![X16 : $i, X17 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.51/0.69      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.51/0.69  thf('14', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (((X0) = (k6_subset_1 @ X0 @ X1))
% 0.51/0.69          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.69  thf('15', plain,
% 0.51/0.69      (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['10', '14'])).
% 0.51/0.69  thf('16', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X4 @ X3)
% 0.51/0.69          | ~ (r2_hidden @ X4 @ X2)
% 0.51/0.69          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.51/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.51/0.69  thf('17', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.51/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.51/0.69  thf('18', plain,
% 0.51/0.69      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.51/0.69  thf('19', plain,
% 0.51/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.51/0.69          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 0.51/0.69      inference('demod', [status(thm)], ['17', '18'])).
% 0.51/0.69  thf('20', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['15', '19'])).
% 0.51/0.69  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.51/0.69      inference('condensation', [status(thm)], ['20'])).
% 0.51/0.69  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['7', '21'])).
% 0.51/0.69  thf(t29_yellow_6, conjecture,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.51/0.69             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.51/0.69           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i]:
% 0.51/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.69          ( ![B:$i]:
% 0.51/0.69            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.51/0.69                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.51/0.69              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.51/0.69  thf('23', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(t9_waybel_0, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.51/0.69               ( ~( r2_waybel_0 @
% 0.51/0.69                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.51/0.69  thf('24', plain,
% 0.51/0.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X24)
% 0.51/0.69          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.51/0.69          | (r2_waybel_0 @ X25 @ X24 @ 
% 0.51/0.69             (k6_subset_1 @ (u1_struct_0 @ X25) @ X26))
% 0.51/0.69          | (r1_waybel_0 @ X25 @ X24 @ X26)
% 0.51/0.69          | ~ (l1_struct_0 @ X25)
% 0.51/0.69          | (v2_struct_0 @ X25))),
% 0.51/0.69      inference('cnf', [status(esa)], [t9_waybel_0])).
% 0.51/0.69  thf('25', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_A)
% 0.51/0.69          | ~ (l1_struct_0 @ sk_A)
% 0.51/0.69          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.69  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('27', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_A)
% 0.51/0.69          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('demod', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf('28', plain,
% 0.51/0.69      (((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.51/0.69        | (v2_struct_0 @ sk_B_1)
% 0.51/0.69        | (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.51/0.69        | (v2_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup+', [status(thm)], ['22', '27'])).
% 0.51/0.69  thf('29', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('30', plain,
% 0.51/0.69      (((v2_struct_0 @ sk_A)
% 0.51/0.69        | (v2_struct_0 @ sk_B_1)
% 0.51/0.69        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.69  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('32', plain,
% 0.51/0.69      (((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0) | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('clc', [status(thm)], ['30', '31'])).
% 0.51/0.69  thf('33', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('34', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.51/0.69      inference('clc', [status(thm)], ['32', '33'])).
% 0.51/0.69  thf('35', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('36', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(d12_waybel_0, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.51/0.69               ( ![D:$i]:
% 0.51/0.69                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.51/0.69                   ( ?[E:$i]:
% 0.51/0.69                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.51/0.69                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.51/0.69                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.69  thf('37', plain,
% 0.51/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X18)
% 0.51/0.69          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.51/0.69          | (m1_subset_1 @ (sk_D_1 @ X20 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 0.51/0.69          | (r2_waybel_0 @ X19 @ X18 @ X20)
% 0.51/0.69          | ~ (l1_struct_0 @ X19)
% 0.51/0.69          | (v2_struct_0 @ X19))),
% 0.51/0.69      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.51/0.69  thf('38', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_A)
% 0.51/0.69          | ~ (l1_struct_0 @ sk_A)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69             (u1_struct_0 @ sk_B_1))
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.69  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('40', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_A)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69             (u1_struct_0 @ sk_B_1))
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('demod', [status(thm)], ['38', '39'])).
% 0.51/0.69  thf('41', plain,
% 0.51/0.69      (![X18 : $i, X19 : $i, X22 : $i, X23 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X18)
% 0.51/0.69          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.51/0.69          | ~ (r2_waybel_0 @ X19 @ X18 @ X22)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ X19 @ X18 @ (sk_E @ X23 @ X22 @ X18 @ X19)) @ X22)
% 0.51/0.69          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.51/0.69          | ~ (l1_struct_0 @ X19)
% 0.51/0.69          | (v2_struct_0 @ X19))),
% 0.51/0.69      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.51/0.69  thf('42', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | (v2_struct_0 @ X1)
% 0.51/0.69          | ~ (l1_struct_0 @ X1)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.51/0.69             X2)
% 0.51/0.69          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.51/0.69          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.69  thf('43', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.51/0.69          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X2 @ sk_B_1 @ X1)) @ 
% 0.51/0.69             X2)
% 0.51/0.69          | ~ (l1_struct_0 @ X1)
% 0.51/0.69          | (v2_struct_0 @ X1)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.69  thf('44', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | ~ (l1_struct_0 @ sk_A)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.51/0.69             X1)
% 0.51/0.69          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['35', '43'])).
% 0.51/0.69  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('46', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.51/0.69             X1)
% 0.51/0.69          | ~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1))),
% 0.51/0.69      inference('demod', [status(thm)], ['44', '45'])).
% 0.51/0.69  thf('47', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (r2_waybel_0 @ sk_A @ sk_B_1 @ X1)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X1 @ sk_B_1 @ sk_A)) @ 
% 0.51/0.69             X1)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('simplify', [status(thm)], ['46'])).
% 0.51/0.69  thf('48', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ sk_A)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0 @ sk_B_1 @ 
% 0.51/0.69               sk_A)) @ 
% 0.51/0.69             k1_xboole_0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['34', '47'])).
% 0.51/0.69  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.51/0.69      inference('condensation', [status(thm)], ['20'])).
% 0.51/0.69  thf('50', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_A)
% 0.51/0.69          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.51/0.69  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('52', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.51/0.69      inference('clc', [status(thm)], ['50', '51'])).
% 0.51/0.69  thf('53', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('54', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.51/0.69      inference('clc', [status(thm)], ['52', '53'])).
% 0.51/0.69  thf('55', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.51/0.69      inference('clc', [status(thm)], ['52', '53'])).
% 0.51/0.69  thf(existence_m1_subset_1, axiom,
% 0.51/0.69    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.51/0.69  thf('56', plain, (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.51/0.69      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.51/0.69  thf('57', plain,
% 0.51/0.69      (![X18 : $i, X19 : $i, X22 : $i, X23 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X18)
% 0.51/0.69          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.51/0.69          | ~ (r2_waybel_0 @ X19 @ X18 @ X22)
% 0.51/0.69          | (m1_subset_1 @ (sk_E @ X23 @ X22 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 0.51/0.69          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.51/0.69          | ~ (l1_struct_0 @ X19)
% 0.51/0.69          | (v2_struct_0 @ X19))),
% 0.51/0.69      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.51/0.69  thf('58', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X1)
% 0.51/0.69          | ~ (l1_struct_0 @ X1)
% 0.51/0.69          | (m1_subset_1 @ 
% 0.51/0.69             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.51/0.69             (u1_struct_0 @ X0))
% 0.51/0.69          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.51/0.69          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.51/0.69          | (v2_struct_0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.51/0.69  thf('59', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.51/0.69          | (m1_subset_1 @ 
% 0.51/0.69             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69             (u1_struct_0 @ sk_B_1))
% 0.51/0.69          | ~ (l1_struct_0 @ sk_A)
% 0.51/0.69          | (v2_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['55', '58'])).
% 0.51/0.69  thf('60', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('62', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | (m1_subset_1 @ 
% 0.51/0.69             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69             (u1_struct_0 @ sk_B_1))
% 0.51/0.69          | (v2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.51/0.69  thf('63', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('64', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_A)
% 0.51/0.69          | (m1_subset_1 @ 
% 0.51/0.69             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69             (u1_struct_0 @ sk_B_1)))),
% 0.51/0.69      inference('clc', [status(thm)], ['62', '63'])).
% 0.51/0.69  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('66', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (m1_subset_1 @ 
% 0.51/0.69          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69          (u1_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('clc', [status(thm)], ['64', '65'])).
% 0.51/0.69  thf('67', plain,
% 0.51/0.69      (![X18 : $i, X19 : $i, X22 : $i, X23 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X18)
% 0.51/0.69          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.51/0.69          | ~ (r2_waybel_0 @ X19 @ X18 @ X22)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ X19 @ X18 @ (sk_E @ X23 @ X22 @ X18 @ X19)) @ X22)
% 0.51/0.69          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.51/0.69          | ~ (l1_struct_0 @ X19)
% 0.51/0.69          | (v2_struct_0 @ X19))),
% 0.51/0.69      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.51/0.69  thf('68', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X1)
% 0.51/0.69          | ~ (l1_struct_0 @ X1)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ 
% 0.51/0.69               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69               X2 @ sk_B_1 @ X1)) @ 
% 0.51/0.69             X2)
% 0.51/0.69          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.51/0.69          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.51/0.69          | (v2_struct_0 @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.51/0.69  thf('69', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ 
% 0.51/0.69               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69               X0 @ sk_B_1 @ sk_A)) @ 
% 0.51/0.69             X0)
% 0.51/0.69          | ~ (l1_struct_0 @ sk_A)
% 0.51/0.69          | (v2_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['54', '68'])).
% 0.51/0.69  thf('70', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('72', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_B_1)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ 
% 0.51/0.69               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69               X0 @ sk_B_1 @ sk_A)) @ 
% 0.51/0.69             X0)
% 0.51/0.69          | (v2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.51/0.69  thf('73', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('74', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((v2_struct_0 @ sk_A)
% 0.51/0.69          | (r2_hidden @ 
% 0.51/0.69             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69              (sk_E @ 
% 0.51/0.69               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69               X0 @ sk_B_1 @ sk_A)) @ 
% 0.51/0.69             X0))),
% 0.51/0.69      inference('clc', [status(thm)], ['72', '73'])).
% 0.51/0.69  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('76', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (r2_hidden @ 
% 0.51/0.69          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.51/0.69           (sk_E @ 
% 0.51/0.69            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.51/0.69            X0 @ sk_B_1 @ sk_A)) @ 
% 0.51/0.69          X0)),
% 0.51/0.69      inference('clc', [status(thm)], ['74', '75'])).
% 0.51/0.69  thf('77', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['7', '21'])).
% 0.51/0.69  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.51/0.69      inference('condensation', [status(thm)], ['20'])).
% 0.51/0.69  thf('79', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k6_subset_1 @ X0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['77', '78'])).
% 0.51/0.69  thf('80', plain, ($false), inference('sup-', [status(thm)], ['76', '79'])).
% 0.51/0.69  
% 0.51/0.69  % SZS output end Refutation
% 0.51/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
