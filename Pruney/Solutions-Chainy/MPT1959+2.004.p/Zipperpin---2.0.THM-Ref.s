%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QkAJ2ajwwT

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:09 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 194 expanded)
%              Number of leaves         :   31 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  853 (2778 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ X0 )
      | ( sk_B_1 = X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ ( k3_yellow_0 @ X14 ) @ X13 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v1_yellow_0 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('11',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
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
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X17 @ X15 )
      | ~ ( r1_orders_2 @ X16 @ X18 @ X17 )
      | ~ ( r2_hidden @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('41',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['30','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('45',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('50',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( sk_B @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ X4 @ X4 ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('60',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('63',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('73',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QkAJ2ajwwT
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:39:42 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 154 iterations in 0.107s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.37/0.57  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.37/0.57  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.37/0.57  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(t8_waybel_7, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.37/0.57         ( l1_orders_2 @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.37/0.57             ( v13_waybel_0 @ B @ A ) & 
% 0.37/0.57             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.37/0.57             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.57            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.37/0.57            ( l1_orders_2 @ A ) ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.37/0.57                ( v13_waybel_0 @ B @ A ) & 
% 0.37/0.57                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.37/0.57                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.37/0.57        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.37/0.57       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf(t2_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.57       ( ( A ) = ( B ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((X1) = (X0))
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.57  thf(t1_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.37/0.57          | ((X1) = (X0))
% 0.37/0.57          | (m1_subset_1 @ (sk_C @ X0 @ X1) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t4_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X9 @ X10)
% 0.37/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.37/0.57          | (m1_subset_1 @ X9 @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ X0)
% 0.37/0.57          | ((sk_B_1) = (X0))
% 0.37/0.57          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('eq_fact', [status(thm)], ['8'])).
% 0.37/0.57  thf(t44_yellow_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.37/0.57         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.57           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.37/0.57          | (r1_orders_2 @ X14 @ (k3_yellow_0 @ X14) @ X13)
% 0.37/0.57          | ~ (l1_orders_2 @ X14)
% 0.37/0.57          | ~ (v1_yellow_0 @ X14)
% 0.37/0.57          | ~ (v5_orders_2 @ X14)
% 0.37/0.57          | (v2_struct_0 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v5_orders_2 @ sk_A)
% 0.37/0.57        | ~ (v1_yellow_0 @ sk_A)
% 0.37/0.57        | ~ (l1_orders_2 @ sk_A)
% 0.37/0.57        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.37/0.57           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('12', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('13', plain, ((v1_yellow_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.37/0.57           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.37/0.57  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.37/0.57         (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d20_waybel_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_orders_2 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.37/0.57             ( ![C:$i]:
% 0.37/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.57                 ( ![D:$i]:
% 0.37/0.57                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.57                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.37/0.57                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.57          | ~ (v13_waybel_0 @ X15 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.37/0.57          | (r2_hidden @ X17 @ X15)
% 0.37/0.57          | ~ (r1_orders_2 @ X16 @ X18 @ X17)
% 0.37/0.57          | ~ (r2_hidden @ X18 @ X15)
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.37/0.57          | ~ (l1_orders_2 @ X16))),
% 0.37/0.57      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (l1_orders_2 @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.57          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X1 @ sk_B_1)
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.57  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('25', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.57          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X1 @ sk_B_1)
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57           | (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.57           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.37/0.57           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57           | (r2_hidden @ X0 @ sk_B_1)
% 0.37/0.57           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.57         | (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_B_1)
% 0.37/0.57         | ~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.57              (u1_struct_0 @ sk_A))))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('eq_fact', [status(thm)], ['8'])).
% 0.37/0.57  thf(t2_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         ((r2_hidden @ X7 @ X8)
% 0.37/0.57          | (v1_xboole_0 @ X8)
% 0.37/0.57          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57        | (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.57           (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc1_subset_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.37/0.57          | (v1_xboole_0 @ X2)
% 0.37/0.57          | ~ (v1_xboole_0 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.57  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('38', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('clc', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['33', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((X1) = (X0))
% 0.37/0.57          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.37/0.57          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | ~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_B_1)
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      ((~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_B_1)
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (((~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.57            (u1_struct_0 @ sk_A))
% 0.37/0.57         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('clc', [status(thm)], ['30', '42'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('eq_fact', [status(thm)], ['8'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('clc', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.37/0.57        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['46'])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.37/0.57         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.37/0.57             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['45', '47'])).
% 0.37/0.57  thf(rc3_subset_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ?[B:$i]:
% 0.37/0.57       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.37/0.57  thf('49', plain, (![X4 : $i]: ~ (v1_subset_1 @ (sk_B @ X4) @ X4)),
% 0.37/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (![X4 : $i]: (m1_subset_1 @ (sk_B @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.37/0.57  thf(d7_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i]:
% 0.37/0.57         (((X20) = (X19))
% 0.37/0.57          | (v1_subset_1 @ X20 @ X19)
% 0.37/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.57  thf('53', plain, (![X4 : $i]: ~ (v1_subset_1 @ (sk_B @ X4) @ X4)),
% 0.37/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.37/0.57  thf('54', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.37/0.57      inference('clc', [status(thm)], ['52', '53'])).
% 0.37/0.57  thf('55', plain, (![X4 : $i]: ~ (v1_subset_1 @ X4 @ X4)),
% 0.37/0.57      inference('demod', [status(thm)], ['49', '54'])).
% 0.37/0.57  thf('56', plain,
% 0.37/0.57      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.37/0.57       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['48', '55'])).
% 0.37/0.57  thf('57', plain,
% 0.37/0.57      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.37/0.57       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['46'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i]:
% 0.37/0.57         (((X20) = (X19))
% 0.37/0.57          | (v1_subset_1 @ X20 @ X19)
% 0.37/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf(dt_k3_yellow_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_orders_2 @ A ) =>
% 0.37/0.57       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      (![X12 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (k3_yellow_0 @ X12) @ (u1_struct_0 @ X12))
% 0.37/0.57          | ~ (l1_orders_2 @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         ((r2_hidden @ X7 @ X8)
% 0.37/0.57          | (v1_xboole_0 @ X8)
% 0.37/0.57          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_orders_2 @ X0)
% 0.37/0.57          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.37/0.57          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.37/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57         | ~ (l1_orders_2 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['62', '65'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf('68', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.37/0.57  thf('70', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('71', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('clc', [status(thm)], ['69', '70'])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.37/0.57         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.57      inference('split', [status(esa)], ['46'])).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.37/0.57       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.57  thf('74', plain, ($false),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '73'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
