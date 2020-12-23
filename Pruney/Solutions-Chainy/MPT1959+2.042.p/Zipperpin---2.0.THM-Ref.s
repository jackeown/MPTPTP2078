%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UWnCGTvRsC

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:15 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 274 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          :  959 (4158 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(t8_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ X0 )
      | ( sk_B = X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r1_orders_2 @ X21 @ ( k3_yellow_0 @ X21 ) @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v1_yellow_0 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('11',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r1_orders_2 @ X23 @ X25 @ X24 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('32',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','40'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_tarski @ X9 @ X7 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('43',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('49',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('52',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','54'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('56',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_subset_1 @ X27 @ X26 )
      | ( X27 != X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('57',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_subset_1 @ X26 @ X26 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X26: $i] :
      ~ ( v1_subset_1 @ X26 @ X26 ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('72',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('85',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','68','69','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UWnCGTvRsC
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:39:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 291 iterations in 0.210s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.47/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.64  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.47/0.64  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.47/0.64  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.47/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.47/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.64  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.47/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.64  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.64  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.47/0.64  thf(t8_waybel_7, conjecture,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.64         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.47/0.64         ( l1_orders_2 @ A ) ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.47/0.64             ( v13_waybel_0 @ B @ A ) & 
% 0.47/0.64             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.64           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.47/0.64             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i]:
% 0.47/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.47/0.64            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.47/0.64            ( l1_orders_2 @ A ) ) =>
% 0.47/0.64          ( ![B:$i]:
% 0.47/0.64            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.47/0.64                ( v13_waybel_0 @ B @ A ) & 
% 0.47/0.64                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.64              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.47/0.64                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.47/0.64  thf('0', plain,
% 0.47/0.64      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.47/0.64        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.47/0.64       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf(t2_tarski, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.47/0.64       ( ( A ) = ( B ) ) ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X4 : $i, X5 : $i]:
% 0.47/0.64         (((X5) = (X4))
% 0.47/0.64          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.47/0.64          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_tarski])).
% 0.47/0.64  thf(t1_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [t1_subset])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 0.47/0.64          | ((X1) = (X0))
% 0.47/0.64          | (m1_subset_1 @ (sk_C_1 @ X0 @ X1) @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t4_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.47/0.64       ( m1_subset_1 @ A @ C ) ))).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X16 @ X17)
% 0.47/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.47/0.64          | (m1_subset_1 @ X16 @ X18))),
% 0.47/0.64      inference('cnf', [status(esa)], [t4_subset])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (sk_C_1 @ X0 @ sk_B) @ X0)
% 0.47/0.64          | ((sk_B) = (X0))
% 0.47/0.64          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '7'])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (((m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.64         (u1_struct_0 @ sk_A))
% 0.47/0.64        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('eq_fact', [status(thm)], ['8'])).
% 0.47/0.64  thf(t44_yellow_0, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.47/0.64         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.64           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X20 : $i, X21 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.47/0.64          | (r1_orders_2 @ X21 @ (k3_yellow_0 @ X21) @ X20)
% 0.47/0.64          | ~ (l1_orders_2 @ X21)
% 0.47/0.64          | ~ (v1_yellow_0 @ X21)
% 0.47/0.64          | ~ (v5_orders_2 @ X21)
% 0.47/0.64          | (v2_struct_0 @ X21))),
% 0.47/0.64      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | ~ (v5_orders_2 @ sk_A)
% 0.47/0.64        | ~ (v1_yellow_0 @ sk_A)
% 0.47/0.64        | ~ (l1_orders_2 @ sk_A)
% 0.47/0.64        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.47/0.64           (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('12', plain, ((v5_orders_2 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('13', plain, ((v1_yellow_0 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.47/0.64           (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.47/0.64  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.47/0.64         (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.64        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('clc', [status(thm)], ['15', '16'])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(d20_waybel_0, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( l1_orders_2 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.64           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.47/0.64             ( ![C:$i]:
% 0.47/0.64               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.64                 ( ![D:$i]:
% 0.47/0.64                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.64                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.47/0.64                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.47/0.64          | ~ (v13_waybel_0 @ X22 @ X23)
% 0.47/0.64          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.47/0.64          | (r2_hidden @ X24 @ X22)
% 0.47/0.64          | ~ (r1_orders_2 @ X23 @ X25 @ X24)
% 0.47/0.64          | ~ (r2_hidden @ X25 @ X22)
% 0.47/0.64          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.47/0.64          | ~ (l1_orders_2 @ X23))),
% 0.47/0.64      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (l1_orders_2 @ sk_A)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ sk_B)
% 0.47/0.64          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.47/0.64          | (r2_hidden @ X1 @ sk_B)
% 0.47/0.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.47/0.64          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.64  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('25', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ sk_B)
% 0.47/0.64          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.47/0.64          | (r2_hidden @ X1 @ sk_B)
% 0.47/0.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64           | (r2_hidden @ X0 @ sk_B)
% 0.47/0.64           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.47/0.64           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['20', '26'])).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64           | (r2_hidden @ X0 @ sk_B)
% 0.47/0.64           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.47/0.64         | (r2_hidden @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.64         | ~ (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.64              (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '29'])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (((m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.64         (u1_struct_0 @ sk_A))
% 0.47/0.64        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('eq_fact', [status(thm)], ['8'])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      ((((r2_hidden @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.64         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('clc', [status(thm)], ['30', '31'])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(d2_subset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( v1_xboole_0 @ A ) =>
% 0.47/0.64         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.47/0.64       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.64         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.64  thf('34', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X11 @ X12)
% 0.47/0.64          | (r2_hidden @ X11 @ X12)
% 0.47/0.64          | (v1_xboole_0 @ X12))),
% 0.47/0.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.64        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (![X12 : $i, X13 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X13 @ X12)
% 0.47/0.64          | (v1_xboole_0 @ X13)
% 0.47/0.64          | ~ (v1_xboole_0 @ X12))),
% 0.47/0.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.64        | (v1_xboole_0 @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.64  thf('39', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('40', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('clc', [status(thm)], ['38', '39'])).
% 0.47/0.64  thf('41', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('clc', [status(thm)], ['35', '40'])).
% 0.47/0.64  thf(d1_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.47/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X9 @ X8)
% 0.47/0.64          | (r1_tarski @ X9 @ X7)
% 0.47/0.64          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X7 : $i, X9 : $i]:
% 0.47/0.64         ((r1_tarski @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['42'])).
% 0.47/0.64  thf('44', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['41', '43'])).
% 0.47/0.64  thf(d3_tarski, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.64          | (r2_hidden @ X0 @ X2)
% 0.47/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.47/0.64         | (r2_hidden @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.64            (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['32', '46'])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (![X4 : $i, X5 : $i]:
% 0.47/0.64         (((X5) = (X4))
% 0.47/0.64          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.47/0.64          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_tarski])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.47/0.64         | ~ (r2_hidden @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.64         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      (((~ (r2_hidden @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.64         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      ((((r2_hidden @ (sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.47/0.64         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('clc', [status(thm)], ['30', '31'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.47/0.64         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.47/0.64        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.47/0.64         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('split', [status(esa)], ['53'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      (((v1_subset_1 @ sk_B @ sk_B))
% 0.47/0.64         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.47/0.64             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['52', '54'])).
% 0.47/0.64  thf(d7_subset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.64       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X26 : $i, X27 : $i]:
% 0.47/0.64         (~ (v1_subset_1 @ X27 @ X26)
% 0.47/0.64          | ((X27) != (X26))
% 0.47/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      (![X26 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))
% 0.47/0.64          | ~ (v1_subset_1 @ X26 @ X26))),
% 0.47/0.64      inference('simplify', [status(thm)], ['56'])).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      (![X1 : $i, X3 : $i]:
% 0.47/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      (![X1 : $i, X3 : $i]:
% 0.47/0.64         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.64  thf('61', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.64      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.64         (~ (r1_tarski @ X6 @ X7)
% 0.47/0.64          | (r2_hidden @ X6 @ X8)
% 0.47/0.64          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i]:
% 0.47/0.64         ((r2_hidden @ X6 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.47/0.64      inference('simplify', [status(thm)], ['62'])).
% 0.47/0.64  thf('64', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['61', '63'])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [t1_subset])).
% 0.47/0.64  thf('66', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.64  thf('67', plain, (![X26 : $i]: ~ (v1_subset_1 @ X26 @ X26)),
% 0.47/0.64      inference('demod', [status(thm)], ['57', '66'])).
% 0.47/0.64  thf('68', plain,
% 0.47/0.64      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.47/0.64       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['55', '67'])).
% 0.47/0.64  thf('69', plain,
% 0.47/0.64      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.47/0.64       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('split', [status(esa)], ['53'])).
% 0.47/0.64  thf('70', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('71', plain,
% 0.47/0.64      (![X26 : $i, X27 : $i]:
% 0.47/0.64         (((X27) = (X26))
% 0.47/0.64          | (v1_subset_1 @ X27 @ X26)
% 0.47/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.47/0.64        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.47/0.64  thf('73', plain,
% 0.47/0.64      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.47/0.64         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('74', plain,
% 0.47/0.64      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.47/0.64         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.64  thf(dt_k3_yellow_0, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( l1_orders_2 @ A ) =>
% 0.47/0.64       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.47/0.64  thf('75', plain,
% 0.47/0.64      (![X19 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (k3_yellow_0 @ X19) @ (u1_struct_0 @ X19))
% 0.47/0.64          | ~ (l1_orders_2 @ X19))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.47/0.64  thf('76', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X11 @ X12)
% 0.47/0.64          | (r2_hidden @ X11 @ X12)
% 0.47/0.64          | (v1_xboole_0 @ X12))),
% 0.47/0.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.47/0.64  thf('77', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_orders_2 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.64          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.64  thf('78', plain,
% 0.47/0.64      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | ~ (l1_orders_2 @ sk_A)))
% 0.47/0.64         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('sup+', [status(thm)], ['74', '77'])).
% 0.47/0.64  thf('79', plain,
% 0.47/0.64      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.47/0.64         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.64  thf('80', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.47/0.64         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.47/0.64  thf('82', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('83', plain,
% 0.47/0.64      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.47/0.64         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('clc', [status(thm)], ['81', '82'])).
% 0.47/0.64  thf('84', plain,
% 0.47/0.64      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.47/0.64         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['53'])).
% 0.47/0.64  thf('85', plain,
% 0.47/0.64      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.47/0.64       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['83', '84'])).
% 0.47/0.64  thf('86', plain, ($false),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['1', '68', '69', '85'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
