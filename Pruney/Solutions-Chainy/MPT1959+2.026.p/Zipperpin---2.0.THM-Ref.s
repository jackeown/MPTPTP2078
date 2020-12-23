%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YT2GIhRsiq

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:12 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 274 expanded)
%              Number of leaves         :   44 (  95 expanded)
%              Depth                    :   22
%              Number of atoms          : 1556 (4372 expanded)
%              Number of equality atoms :   45 (  58 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( sk_B = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('9',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t39_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ( k1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B )
            & ( ( k2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B ) ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( ( k1_yellow_0 @ X22 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) )
        = X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_0])).

thf('11',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('19',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( ( k2_yellow_0 @ X22 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) )
        = X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_0])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_yellow_0 @ sk_A ) ) )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X12: $i] :
      ( ( ( k3_yellow_0 @ X12 )
        = ( k1_yellow_0 @ X12 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( ( k2_yellow_0 @ X22 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) )
        = X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k3_yellow_0 @ X0 ) ) )
        = ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k3_yellow_0 @ X0 ) ) )
        = ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( ( k3_yellow_0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( ( k3_yellow_0 @ sk_A )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k3_yellow_0 @ sk_A )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( ( k1_yellow_0 @ X22 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) )
        = X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X23: $i] :
      ( ( r1_yellow_0 @ X23 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v1_yellow_0 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(t38_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            & ( r2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r1_yellow_0 @ X20 @ ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_orders_2 @ X16 @ ( k1_yellow_0 @ X16 @ X17 ) @ ( k1_yellow_0 @ X16 @ X18 ) )
      | ~ ( r1_yellow_0 @ X16 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X16 @ X17 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( r1_yellow_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k1_yellow_0 @ X1 @ X0 ) ) )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k1_yellow_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k1_yellow_0 @ X1 @ X0 ) ) ) )
      | ~ ( r1_tarski @ X2 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k1_yellow_0 @ X1 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ X1 @ X2 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k1_yellow_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['45','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ! [X0: $i] :
        ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( r2_hidden @ X26 @ X24 )
      | ~ ( r1_orders_2 @ X25 @ X27 @ X26 )
      | ~ ( r2_hidden @ X27 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','82'])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['17','85'])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('89',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['86','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','93'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('95',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('96',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('97',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['92'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('101',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( v1_subset_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('102',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('105',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('106',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['92'])).

thf('115',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','98','99','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YT2GIhRsiq
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.64/1.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.64/1.89  % Solved by: fo/fo7.sh
% 1.64/1.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.89  % done 1047 iterations in 1.429s
% 1.64/1.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.64/1.89  % SZS output start Refutation
% 1.64/1.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.89  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 1.64/1.89  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.64/1.89  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 1.64/1.89  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 1.64/1.89  thf(k2_yellow_0_type, type, k2_yellow_0: $i > $i > $i).
% 1.64/1.89  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.64/1.89  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 1.64/1.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.64/1.89  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.89  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.89  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.64/1.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.64/1.89  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.64/1.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.64/1.89  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.64/1.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.64/1.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.64/1.89  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.64/1.89  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.64/1.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.64/1.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.64/1.89  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.64/1.89  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.64/1.89  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 1.64/1.89  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.64/1.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.64/1.89  thf(t8_waybel_7, conjecture,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.64/1.89         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 1.64/1.89         ( l1_orders_2 @ A ) ) =>
% 1.64/1.89       ( ![B:$i]:
% 1.64/1.89         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 1.64/1.89             ( v13_waybel_0 @ B @ A ) & 
% 1.64/1.89             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.89           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 1.64/1.89             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 1.64/1.89  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.89    (~( ![A:$i]:
% 1.64/1.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.64/1.89            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 1.64/1.89            ( l1_orders_2 @ A ) ) =>
% 1.64/1.89          ( ![B:$i]:
% 1.64/1.89            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 1.64/1.89                ( v13_waybel_0 @ B @ A ) & 
% 1.64/1.89                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.64/1.89              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 1.64/1.89                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 1.64/1.89    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 1.64/1.89  thf('0', plain,
% 1.64/1.89      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 1.64/1.89        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('1', plain,
% 1.64/1.89      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 1.64/1.89       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('split', [status(esa)], ['0'])).
% 1.64/1.89  thf(t2_tarski, axiom,
% 1.64/1.89    (![A:$i,B:$i]:
% 1.64/1.89     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 1.64/1.89       ( ( A ) = ( B ) ) ))).
% 1.64/1.89  thf('2', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (((X1) = (X0))
% 1.64/1.89          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 1.64/1.89          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.64/1.89      inference('cnf', [status(esa)], [t2_tarski])).
% 1.64/1.89  thf('3', plain,
% 1.64/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf(l3_subset_1, axiom,
% 1.64/1.89    (![A:$i,B:$i]:
% 1.64/1.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.64/1.89  thf('4', plain,
% 1.64/1.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.64/1.89         (~ (r2_hidden @ X4 @ X5)
% 1.64/1.89          | (r2_hidden @ X4 @ X6)
% 1.64/1.89          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.64/1.89      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.64/1.89  thf('5', plain,
% 1.64/1.89      (![X0 : $i]:
% 1.64/1.89         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.64/1.89      inference('sup-', [status(thm)], ['3', '4'])).
% 1.64/1.89  thf('6', plain,
% 1.64/1.89      (![X0 : $i]:
% 1.64/1.89         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ X0)
% 1.64/1.89          | ((sk_B) = (X0))
% 1.64/1.89          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['2', '5'])).
% 1.64/1.89  thf('7', plain,
% 1.64/1.89      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.89         (u1_struct_0 @ sk_A))
% 1.64/1.89        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('eq_fact', [status(thm)], ['6'])).
% 1.64/1.89  thf(t1_subset, axiom,
% 1.64/1.89    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.64/1.89  thf('8', plain,
% 1.64/1.89      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 1.64/1.89      inference('cnf', [status(esa)], [t1_subset])).
% 1.64/1.89  thf('9', plain,
% 1.64/1.89      ((((sk_B) = (u1_struct_0 @ sk_A))
% 1.64/1.89        | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.89           (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['7', '8'])).
% 1.64/1.89  thf(t39_yellow_0, axiom,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.64/1.89         ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.64/1.89       ( ![B:$i]:
% 1.64/1.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.64/1.89           ( ( ( k1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 1.64/1.89               ( B ) ) & 
% 1.64/1.89             ( ( k2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 1.64/1.89               ( B ) ) ) ) ) ))).
% 1.64/1.89  thf('10', plain,
% 1.64/1.89      (![X21 : $i, X22 : $i]:
% 1.64/1.89         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.64/1.89          | ((k1_yellow_0 @ X22 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21))
% 1.64/1.89              = (X21))
% 1.64/1.89          | ~ (l1_orders_2 @ X22)
% 1.64/1.89          | ~ (v5_orders_2 @ X22)
% 1.64/1.89          | ~ (v3_orders_2 @ X22)
% 1.64/1.89          | (v2_struct_0 @ X22))),
% 1.64/1.89      inference('cnf', [status(esa)], [t39_yellow_0])).
% 1.64/1.89  thf('11', plain,
% 1.64/1.89      ((((sk_B) = (u1_struct_0 @ sk_A))
% 1.64/1.89        | (v2_struct_0 @ sk_A)
% 1.64/1.89        | ~ (v3_orders_2 @ sk_A)
% 1.64/1.89        | ~ (v5_orders_2 @ sk_A)
% 1.64/1.89        | ~ (l1_orders_2 @ sk_A)
% 1.64/1.89        | ((k1_yellow_0 @ sk_A @ 
% 1.64/1.89            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.89             (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.64/1.89            = (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['9', '10'])).
% 1.64/1.89  thf('12', plain, ((v3_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('15', plain,
% 1.64/1.89      ((((sk_B) = (u1_struct_0 @ sk_A))
% 1.64/1.89        | (v2_struct_0 @ sk_A)
% 1.64/1.89        | ((k1_yellow_0 @ sk_A @ 
% 1.64/1.89            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.89             (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.64/1.89            = (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 1.64/1.89  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('17', plain,
% 1.64/1.89      ((((k1_yellow_0 @ sk_A @ 
% 1.64/1.89          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.89           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.64/1.89          = (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.64/1.89        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('clc', [status(thm)], ['15', '16'])).
% 1.64/1.89  thf(dt_k1_yellow_0, axiom,
% 1.64/1.89    (![A:$i,B:$i]:
% 1.64/1.89     ( ( l1_orders_2 @ A ) =>
% 1.64/1.89       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 1.64/1.89  thf('18', plain,
% 1.64/1.89      (![X13 : $i, X14 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X13)
% 1.64/1.89          | (m1_subset_1 @ (k1_yellow_0 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.64/1.89      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.64/1.89  thf('19', plain,
% 1.64/1.89      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('split', [status(esa)], ['0'])).
% 1.64/1.89  thf('20', plain,
% 1.64/1.89      (![X0 : $i]:
% 1.64/1.89         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.64/1.89      inference('sup-', [status(thm)], ['3', '4'])).
% 1.64/1.89  thf('21', plain,
% 1.64/1.89      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['19', '20'])).
% 1.64/1.89  thf('22', plain,
% 1.64/1.89      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 1.64/1.89      inference('cnf', [status(esa)], [t1_subset])).
% 1.64/1.89  thf('23', plain,
% 1.64/1.89      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['21', '22'])).
% 1.64/1.89  thf('24', plain,
% 1.64/1.89      (![X21 : $i, X22 : $i]:
% 1.64/1.89         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.64/1.89          | ((k2_yellow_0 @ X22 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21))
% 1.64/1.89              = (X21))
% 1.64/1.89          | ~ (l1_orders_2 @ X22)
% 1.64/1.89          | ~ (v5_orders_2 @ X22)
% 1.64/1.89          | ~ (v3_orders_2 @ X22)
% 1.64/1.89          | (v2_struct_0 @ X22))),
% 1.64/1.89      inference('cnf', [status(esa)], [t39_yellow_0])).
% 1.64/1.89  thf('25', plain,
% 1.64/1.89      ((((v2_struct_0 @ sk_A)
% 1.64/1.89         | ~ (v3_orders_2 @ sk_A)
% 1.64/1.89         | ~ (v5_orders_2 @ sk_A)
% 1.64/1.89         | ~ (l1_orders_2 @ sk_A)
% 1.64/1.89         | ((k2_yellow_0 @ sk_A @ 
% 1.64/1.89             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (k3_yellow_0 @ sk_A)))
% 1.64/1.89             = (k3_yellow_0 @ sk_A))))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['23', '24'])).
% 1.64/1.89  thf('26', plain, ((v3_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('27', plain, ((v5_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('29', plain,
% 1.64/1.89      ((((v2_struct_0 @ sk_A)
% 1.64/1.89         | ((k2_yellow_0 @ sk_A @ 
% 1.64/1.89             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (k3_yellow_0 @ sk_A)))
% 1.64/1.89             = (k3_yellow_0 @ sk_A))))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 1.64/1.89  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('31', plain,
% 1.64/1.89      ((((k2_yellow_0 @ sk_A @ 
% 1.64/1.89          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (k3_yellow_0 @ sk_A)))
% 1.64/1.89          = (k3_yellow_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('clc', [status(thm)], ['29', '30'])).
% 1.64/1.89  thf(d11_yellow_0, axiom,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( l1_orders_2 @ A ) =>
% 1.64/1.89       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 1.64/1.89  thf('32', plain,
% 1.64/1.89      (![X12 : $i]:
% 1.64/1.89         (((k3_yellow_0 @ X12) = (k1_yellow_0 @ X12 @ k1_xboole_0))
% 1.64/1.89          | ~ (l1_orders_2 @ X12))),
% 1.64/1.89      inference('cnf', [status(esa)], [d11_yellow_0])).
% 1.64/1.89  thf('33', plain,
% 1.64/1.89      (![X13 : $i, X14 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X13)
% 1.64/1.89          | (m1_subset_1 @ (k1_yellow_0 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.64/1.89      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.64/1.89  thf('34', plain,
% 1.64/1.89      (![X21 : $i, X22 : $i]:
% 1.64/1.89         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.64/1.89          | ((k2_yellow_0 @ X22 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21))
% 1.64/1.89              = (X21))
% 1.64/1.89          | ~ (l1_orders_2 @ X22)
% 1.64/1.89          | ~ (v5_orders_2 @ X22)
% 1.64/1.89          | ~ (v3_orders_2 @ X22)
% 1.64/1.89          | (v2_struct_0 @ X22))),
% 1.64/1.89      inference('cnf', [status(esa)], [t39_yellow_0])).
% 1.64/1.89  thf('35', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | ((k2_yellow_0 @ X0 @ 
% 1.64/1.89              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))
% 1.64/1.89              = (k1_yellow_0 @ X0 @ X1)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['33', '34'])).
% 1.64/1.89  thf('36', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (((k2_yellow_0 @ X0 @ 
% 1.64/1.89            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))
% 1.64/1.89            = (k1_yellow_0 @ X0 @ X1))
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0))),
% 1.64/1.89      inference('simplify', [status(thm)], ['35'])).
% 1.64/1.89  thf('37', plain,
% 1.64/1.89      (![X0 : $i]:
% 1.64/1.89         (((k2_yellow_0 @ X0 @ 
% 1.64/1.89            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k3_yellow_0 @ X0)))
% 1.64/1.89            = (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | ~ (v5_orders_2 @ X0))),
% 1.64/1.89      inference('sup+', [status(thm)], ['32', '36'])).
% 1.64/1.89  thf('38', plain,
% 1.64/1.89      (![X0 : $i]:
% 1.64/1.89         (~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | ((k2_yellow_0 @ X0 @ 
% 1.64/1.89              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k3_yellow_0 @ X0)))
% 1.64/1.89              = (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 1.64/1.89      inference('simplify', [status(thm)], ['37'])).
% 1.64/1.89  thf('39', plain,
% 1.64/1.89      (((((k3_yellow_0 @ sk_A) = (k1_yellow_0 @ sk_A @ k1_xboole_0))
% 1.64/1.89         | ~ (l1_orders_2 @ sk_A)
% 1.64/1.89         | (v2_struct_0 @ sk_A)
% 1.64/1.89         | ~ (v3_orders_2 @ sk_A)
% 1.64/1.89         | ~ (v5_orders_2 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup+', [status(thm)], ['31', '38'])).
% 1.64/1.89  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('41', plain, ((v3_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('43', plain,
% 1.64/1.89      (((((k3_yellow_0 @ sk_A) = (k1_yellow_0 @ sk_A @ k1_xboole_0))
% 1.64/1.89         | (v2_struct_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 1.64/1.89  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('45', plain,
% 1.64/1.89      ((((k3_yellow_0 @ sk_A) = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('clc', [status(thm)], ['43', '44'])).
% 1.64/1.89  thf('46', plain,
% 1.64/1.89      (![X13 : $i, X14 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X13)
% 1.64/1.89          | (m1_subset_1 @ (k1_yellow_0 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.64/1.89      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.64/1.89  thf('47', plain,
% 1.64/1.89      (![X21 : $i, X22 : $i]:
% 1.64/1.89         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.64/1.89          | ((k1_yellow_0 @ X22 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21))
% 1.64/1.89              = (X21))
% 1.64/1.89          | ~ (l1_orders_2 @ X22)
% 1.64/1.89          | ~ (v5_orders_2 @ X22)
% 1.64/1.89          | ~ (v3_orders_2 @ X22)
% 1.64/1.89          | (v2_struct_0 @ X22))),
% 1.64/1.89      inference('cnf', [status(esa)], [t39_yellow_0])).
% 1.64/1.89  thf('48', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | ((k1_yellow_0 @ X0 @ 
% 1.64/1.89              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))
% 1.64/1.89              = (k1_yellow_0 @ X0 @ X1)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['46', '47'])).
% 1.64/1.89  thf('49', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (((k1_yellow_0 @ X0 @ 
% 1.64/1.89            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))
% 1.64/1.89            = (k1_yellow_0 @ X0 @ X1))
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0))),
% 1.64/1.89      inference('simplify', [status(thm)], ['48'])).
% 1.64/1.89  thf(t42_yellow_0, axiom,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 1.64/1.89         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.64/1.89       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 1.64/1.89         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 1.64/1.89  thf('50', plain,
% 1.64/1.89      (![X23 : $i]:
% 1.64/1.89         ((r1_yellow_0 @ X23 @ k1_xboole_0)
% 1.64/1.89          | ~ (l1_orders_2 @ X23)
% 1.64/1.89          | ~ (v1_yellow_0 @ X23)
% 1.64/1.89          | ~ (v5_orders_2 @ X23)
% 1.64/1.89          | (v2_struct_0 @ X23))),
% 1.64/1.89      inference('cnf', [status(esa)], [t42_yellow_0])).
% 1.64/1.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.64/1.89  thf('51', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.64/1.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.64/1.89  thf('52', plain,
% 1.64/1.89      (![X13 : $i, X14 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X13)
% 1.64/1.89          | (m1_subset_1 @ (k1_yellow_0 @ X13 @ X14) @ (u1_struct_0 @ X13)))),
% 1.64/1.89      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.64/1.89  thf(t38_yellow_0, axiom,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.64/1.89         ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.64/1.89       ( ![B:$i]:
% 1.64/1.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.64/1.89           ( ( r1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) & 
% 1.64/1.89             ( r2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.64/1.89  thf('53', plain,
% 1.64/1.89      (![X19 : $i, X20 : $i]:
% 1.64/1.89         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 1.64/1.89          | (r1_yellow_0 @ X20 @ (k6_domain_1 @ (u1_struct_0 @ X20) @ X19))
% 1.64/1.89          | ~ (l1_orders_2 @ X20)
% 1.64/1.89          | ~ (v5_orders_2 @ X20)
% 1.64/1.89          | ~ (v3_orders_2 @ X20)
% 1.64/1.89          | (v2_struct_0 @ X20))),
% 1.64/1.89      inference('cnf', [status(esa)], [t38_yellow_0])).
% 1.64/1.89  thf('54', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | (r1_yellow_0 @ X0 @ 
% 1.64/1.89             (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))))),
% 1.64/1.89      inference('sup-', [status(thm)], ['52', '53'])).
% 1.64/1.89  thf('55', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((r1_yellow_0 @ X0 @ 
% 1.64/1.89           (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0))),
% 1.64/1.89      inference('simplify', [status(thm)], ['54'])).
% 1.64/1.89  thf(t34_yellow_0, axiom,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( l1_orders_2 @ A ) =>
% 1.64/1.89       ( ![B:$i,C:$i]:
% 1.64/1.89         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 1.64/1.89             ( r1_yellow_0 @ A @ C ) ) =>
% 1.64/1.89           ( r1_orders_2 @
% 1.64/1.89             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 1.64/1.89  thf('56', plain,
% 1.64/1.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.64/1.89         ((r1_orders_2 @ X16 @ (k1_yellow_0 @ X16 @ X17) @ 
% 1.64/1.89           (k1_yellow_0 @ X16 @ X18))
% 1.64/1.89          | ~ (r1_yellow_0 @ X16 @ X18)
% 1.64/1.89          | ~ (r1_tarski @ X17 @ X18)
% 1.64/1.89          | ~ (r1_yellow_0 @ X16 @ X17)
% 1.64/1.89          | ~ (l1_orders_2 @ X16))),
% 1.64/1.89      inference('cnf', [status(esa)], [t34_yellow_0])).
% 1.64/1.89  thf('57', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X1)
% 1.64/1.89          | (v2_struct_0 @ X1)
% 1.64/1.89          | ~ (v3_orders_2 @ X1)
% 1.64/1.89          | ~ (v5_orders_2 @ X1)
% 1.64/1.89          | ~ (l1_orders_2 @ X1)
% 1.64/1.89          | ~ (r1_yellow_0 @ X1 @ X2)
% 1.64/1.89          | ~ (r1_tarski @ X2 @ 
% 1.64/1.89               (k6_domain_1 @ (u1_struct_0 @ X1) @ (k1_yellow_0 @ X1 @ X0)))
% 1.64/1.89          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 1.64/1.89             (k1_yellow_0 @ X1 @ 
% 1.64/1.89              (k6_domain_1 @ (u1_struct_0 @ X1) @ (k1_yellow_0 @ X1 @ X0)))))),
% 1.64/1.89      inference('sup-', [status(thm)], ['55', '56'])).
% 1.64/1.89  thf('58', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.89         ((r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 1.64/1.89           (k1_yellow_0 @ X1 @ 
% 1.64/1.89            (k6_domain_1 @ (u1_struct_0 @ X1) @ (k1_yellow_0 @ X1 @ X0))))
% 1.64/1.89          | ~ (r1_tarski @ X2 @ 
% 1.64/1.89               (k6_domain_1 @ (u1_struct_0 @ X1) @ (k1_yellow_0 @ X1 @ X0)))
% 1.64/1.89          | ~ (r1_yellow_0 @ X1 @ X2)
% 1.64/1.89          | ~ (v5_orders_2 @ X1)
% 1.64/1.89          | ~ (v3_orders_2 @ X1)
% 1.64/1.89          | (v2_struct_0 @ X1)
% 1.64/1.89          | ~ (l1_orders_2 @ X1))),
% 1.64/1.89      inference('simplify', [status(thm)], ['57'])).
% 1.64/1.89  thf('59', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X1)
% 1.64/1.89          | (v2_struct_0 @ X1)
% 1.64/1.89          | ~ (v3_orders_2 @ X1)
% 1.64/1.89          | ~ (v5_orders_2 @ X1)
% 1.64/1.89          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 1.64/1.89          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 1.64/1.89             (k1_yellow_0 @ X1 @ 
% 1.64/1.89              (k6_domain_1 @ (u1_struct_0 @ X1) @ (k1_yellow_0 @ X1 @ X0)))))),
% 1.64/1.89      inference('sup-', [status(thm)], ['51', '58'])).
% 1.64/1.89  thf('60', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((v2_struct_0 @ X0)
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (v1_yellow_0 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.64/1.89             (k1_yellow_0 @ X0 @ 
% 1.64/1.89              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))))
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | ~ (v3_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0)
% 1.64/1.89          | ~ (l1_orders_2 @ X0))),
% 1.64/1.89      inference('sup-', [status(thm)], ['50', '59'])).
% 1.64/1.89  thf('61', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (v3_orders_2 @ X0)
% 1.64/1.89          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.64/1.89             (k1_yellow_0 @ X0 @ 
% 1.64/1.89              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))))
% 1.64/1.89          | ~ (l1_orders_2 @ X0)
% 1.64/1.89          | ~ (v1_yellow_0 @ X0)
% 1.64/1.89          | ~ (v5_orders_2 @ X0)
% 1.64/1.89          | (v2_struct_0 @ X0))),
% 1.64/1.89      inference('simplify', [status(thm)], ['60'])).
% 1.64/1.89  thf('62', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         ((r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 1.64/1.89           (k1_yellow_0 @ X1 @ X0))
% 1.64/1.89          | ~ (l1_orders_2 @ X1)
% 1.64/1.89          | (v2_struct_0 @ X1)
% 1.64/1.89          | ~ (v3_orders_2 @ X1)
% 1.64/1.89          | ~ (v5_orders_2 @ X1)
% 1.64/1.89          | (v2_struct_0 @ X1)
% 1.64/1.89          | ~ (v5_orders_2 @ X1)
% 1.64/1.89          | ~ (v1_yellow_0 @ X1)
% 1.64/1.89          | ~ (l1_orders_2 @ X1)
% 1.64/1.89          | ~ (v3_orders_2 @ X1))),
% 1.64/1.89      inference('sup+', [status(thm)], ['49', '61'])).
% 1.64/1.89  thf('63', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (v1_yellow_0 @ X1)
% 1.64/1.89          | ~ (v5_orders_2 @ X1)
% 1.64/1.89          | ~ (v3_orders_2 @ X1)
% 1.64/1.89          | (v2_struct_0 @ X1)
% 1.64/1.89          | ~ (l1_orders_2 @ X1)
% 1.64/1.89          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 1.64/1.89             (k1_yellow_0 @ X1 @ X0)))),
% 1.64/1.89      inference('simplify', [status(thm)], ['62'])).
% 1.64/1.89  thf('64', plain,
% 1.64/1.89      ((![X0 : $i]:
% 1.64/1.89          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.64/1.89            (k1_yellow_0 @ sk_A @ X0))
% 1.64/1.89           | ~ (l1_orders_2 @ sk_A)
% 1.64/1.89           | (v2_struct_0 @ sk_A)
% 1.64/1.89           | ~ (v3_orders_2 @ sk_A)
% 1.64/1.89           | ~ (v5_orders_2 @ sk_A)
% 1.64/1.89           | ~ (v1_yellow_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup+', [status(thm)], ['45', '63'])).
% 1.64/1.89  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('67', plain, ((v5_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('68', plain, ((v1_yellow_0 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('69', plain,
% 1.64/1.89      ((![X0 : $i]:
% 1.64/1.89          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.64/1.89            (k1_yellow_0 @ sk_A @ X0))
% 1.64/1.89           | (v2_struct_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 1.64/1.89  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('71', plain,
% 1.64/1.89      ((![X0 : $i]:
% 1.64/1.89          (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.64/1.89           (k1_yellow_0 @ sk_A @ X0)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('clc', [status(thm)], ['69', '70'])).
% 1.64/1.89  thf('72', plain,
% 1.64/1.89      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['21', '22'])).
% 1.64/1.89  thf('73', plain,
% 1.64/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf(d20_waybel_0, axiom,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( l1_orders_2 @ A ) =>
% 1.64/1.89       ( ![B:$i]:
% 1.64/1.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.64/1.89           ( ( v13_waybel_0 @ B @ A ) <=>
% 1.64/1.89             ( ![C:$i]:
% 1.64/1.89               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.64/1.89                 ( ![D:$i]:
% 1.64/1.89                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.64/1.89                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 1.64/1.89                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 1.64/1.89  thf('74', plain,
% 1.64/1.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.64/1.89         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.64/1.89          | ~ (v13_waybel_0 @ X24 @ X25)
% 1.64/1.89          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 1.64/1.89          | (r2_hidden @ X26 @ X24)
% 1.64/1.89          | ~ (r1_orders_2 @ X25 @ X27 @ X26)
% 1.64/1.89          | ~ (r2_hidden @ X27 @ X24)
% 1.64/1.89          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 1.64/1.89          | ~ (l1_orders_2 @ X25))),
% 1.64/1.89      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.64/1.89  thf('75', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ sk_A)
% 1.64/1.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.64/1.89          | ~ (r2_hidden @ X0 @ sk_B)
% 1.64/1.89          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 1.64/1.89          | (r2_hidden @ X1 @ sk_B)
% 1.64/1.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.64/1.89          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 1.64/1.89      inference('sup-', [status(thm)], ['73', '74'])).
% 1.64/1.89  thf('76', plain, ((l1_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('77', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('78', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.64/1.89          | ~ (r2_hidden @ X0 @ sk_B)
% 1.64/1.89          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 1.64/1.89          | (r2_hidden @ X1 @ sk_B)
% 1.64/1.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.64/1.89  thf('79', plain,
% 1.64/1.89      ((![X0 : $i]:
% 1.64/1.89          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.64/1.89           | (r2_hidden @ X0 @ sk_B)
% 1.64/1.89           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.64/1.89           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['72', '78'])).
% 1.64/1.89  thf('80', plain,
% 1.64/1.89      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('split', [status(esa)], ['0'])).
% 1.64/1.89  thf('81', plain,
% 1.64/1.89      ((![X0 : $i]:
% 1.64/1.89          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.64/1.89           | (r2_hidden @ X0 @ sk_B)
% 1.64/1.89           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('demod', [status(thm)], ['79', '80'])).
% 1.64/1.89  thf('82', plain,
% 1.64/1.89      ((![X0 : $i]:
% 1.64/1.89          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)
% 1.64/1.89           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['71', '81'])).
% 1.64/1.89  thf('83', plain,
% 1.64/1.89      ((![X0 : $i]:
% 1.64/1.89          (~ (l1_orders_2 @ sk_A)
% 1.64/1.89           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['18', '82'])).
% 1.64/1.89  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('85', plain,
% 1.64/1.89      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('demod', [status(thm)], ['83', '84'])).
% 1.64/1.89  thf('86', plain,
% 1.64/1.89      ((((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.64/1.89         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup+', [status(thm)], ['17', '85'])).
% 1.64/1.89  thf('87', plain,
% 1.64/1.89      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.64/1.89         (u1_struct_0 @ sk_A))
% 1.64/1.89        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('eq_fact', [status(thm)], ['6'])).
% 1.64/1.89  thf('88', plain,
% 1.64/1.89      (![X0 : $i, X1 : $i]:
% 1.64/1.89         (((X1) = (X0))
% 1.64/1.89          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 1.64/1.89          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.64/1.89      inference('cnf', [status(esa)], [t2_tarski])).
% 1.64/1.89  thf('89', plain,
% 1.64/1.89      ((((sk_B) = (u1_struct_0 @ sk_A))
% 1.64/1.89        | ~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.64/1.89        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['87', '88'])).
% 1.64/1.89  thf('90', plain,
% 1.64/1.89      ((~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.64/1.89        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('simplify', [status(thm)], ['89'])).
% 1.64/1.89  thf('91', plain,
% 1.64/1.89      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('clc', [status(thm)], ['86', '90'])).
% 1.64/1.89  thf('92', plain,
% 1.64/1.89      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 1.64/1.89        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('93', plain,
% 1.64/1.89      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.64/1.89      inference('split', [status(esa)], ['92'])).
% 1.64/1.89  thf('94', plain,
% 1.64/1.89      (((v1_subset_1 @ sk_B @ sk_B))
% 1.64/1.89         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 1.64/1.89             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('sup+', [status(thm)], ['91', '93'])).
% 1.64/1.89  thf(fc14_subset_1, axiom,
% 1.64/1.89    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 1.64/1.89  thf('95', plain, (![X7 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X7) @ X7)),
% 1.64/1.89      inference('cnf', [status(esa)], [fc14_subset_1])).
% 1.64/1.89  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.64/1.89  thf('96', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 1.64/1.89      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.64/1.89  thf('97', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 1.64/1.89      inference('demod', [status(thm)], ['95', '96'])).
% 1.64/1.89  thf('98', plain,
% 1.64/1.89      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 1.64/1.89       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['94', '97'])).
% 1.64/1.89  thf('99', plain,
% 1.64/1.89      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 1.64/1.89       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('split', [status(esa)], ['92'])).
% 1.64/1.89  thf('100', plain,
% 1.64/1.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf(d7_subset_1, axiom,
% 1.64/1.89    (![A:$i,B:$i]:
% 1.64/1.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.89       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 1.64/1.89  thf('101', plain,
% 1.64/1.89      (![X28 : $i, X29 : $i]:
% 1.64/1.89         (((X29) = (X28))
% 1.64/1.89          | (v1_subset_1 @ X29 @ X28)
% 1.64/1.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 1.64/1.89      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.64/1.89  thf('102', plain,
% 1.64/1.89      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.64/1.89        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['100', '101'])).
% 1.64/1.89  thf('103', plain,
% 1.64/1.89      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.64/1.89      inference('split', [status(esa)], ['0'])).
% 1.64/1.89  thf('104', plain,
% 1.64/1.89      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.64/1.89      inference('sup-', [status(thm)], ['102', '103'])).
% 1.64/1.89  thf(dt_k3_yellow_0, axiom,
% 1.64/1.89    (![A:$i]:
% 1.64/1.89     ( ( l1_orders_2 @ A ) =>
% 1.64/1.89       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 1.64/1.89  thf('105', plain,
% 1.64/1.89      (![X15 : $i]:
% 1.64/1.89         ((m1_subset_1 @ (k3_yellow_0 @ X15) @ (u1_struct_0 @ X15))
% 1.64/1.89          | ~ (l1_orders_2 @ X15))),
% 1.64/1.89      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 1.64/1.89  thf(t2_subset, axiom,
% 1.64/1.89    (![A:$i,B:$i]:
% 1.64/1.89     ( ( m1_subset_1 @ A @ B ) =>
% 1.64/1.89       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.64/1.89  thf('106', plain,
% 1.64/1.89      (![X10 : $i, X11 : $i]:
% 1.64/1.89         ((r2_hidden @ X10 @ X11)
% 1.64/1.89          | (v1_xboole_0 @ X11)
% 1.64/1.89          | ~ (m1_subset_1 @ X10 @ X11))),
% 1.64/1.89      inference('cnf', [status(esa)], [t2_subset])).
% 1.64/1.89  thf('107', plain,
% 1.64/1.89      (![X0 : $i]:
% 1.64/1.89         (~ (l1_orders_2 @ X0)
% 1.64/1.89          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.64/1.89          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['105', '106'])).
% 1.64/1.89  thf('108', plain,
% 1.64/1.89      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 1.64/1.89         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.64/1.89         | ~ (l1_orders_2 @ sk_A)))
% 1.64/1.89         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.64/1.89      inference('sup+', [status(thm)], ['104', '107'])).
% 1.64/1.89  thf('109', plain,
% 1.64/1.89      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 1.64/1.89         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.64/1.89      inference('sup-', [status(thm)], ['102', '103'])).
% 1.64/1.89  thf('110', plain, ((l1_orders_2 @ sk_A)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('111', plain,
% 1.64/1.89      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 1.64/1.89         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.64/1.89      inference('demod', [status(thm)], ['108', '109', '110'])).
% 1.64/1.89  thf('112', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.64/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.89  thf('113', plain,
% 1.64/1.89      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 1.64/1.89         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.64/1.89      inference('clc', [status(thm)], ['111', '112'])).
% 1.64/1.89  thf('114', plain,
% 1.64/1.89      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 1.64/1.89         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 1.64/1.89      inference('split', [status(esa)], ['92'])).
% 1.64/1.89  thf('115', plain,
% 1.64/1.89      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 1.64/1.89       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.64/1.89      inference('sup-', [status(thm)], ['113', '114'])).
% 1.64/1.89  thf('116', plain, ($false),
% 1.64/1.89      inference('sat_resolution*', [status(thm)], ['1', '98', '99', '115'])).
% 1.64/1.89  
% 1.64/1.89  % SZS output end Refutation
% 1.64/1.89  
% 1.64/1.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
