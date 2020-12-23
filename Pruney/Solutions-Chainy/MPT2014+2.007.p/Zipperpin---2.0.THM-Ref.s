%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4D9Ot8tw0l

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 195 expanded)
%              Number of leaves         :   34 (  72 expanded)
%              Depth                    :   22
%              Number of atoms          :  941 (2770 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t13_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_waybel_9])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( v6_waybel_0 @ ( k4_waybel_9 @ X24 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d7_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( l1_waybel_0 @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( ( l1_waybel_0 @ D @ A )
                    & ( v6_waybel_0 @ D @ A ) )
                 => ( ( D
                      = ( k4_waybel_9 @ A @ B @ C ) )
                  <=> ( ( ( u1_waybel_0 @ A @ D )
                        = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ( r2_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) @ ( k1_toler_1 @ ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ! [E: $i] :
                          ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) )
                        <=> ? [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                              & ( F = E )
                              & ( r1_orders_2 @ B @ C @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B )
    <=> ( ( r1_orders_2 @ B @ C @ F )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( ( v6_waybel_0 @ D @ A )
                    & ( l1_waybel_0 @ D @ A ) )
                 => ( ( D
                      = ( k4_waybel_9 @ A @ B @ C ) )
                  <=> ( ! [E: $i] :
                          ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) )
                        <=> ? [F: $i] :
                              ( zip_tseitin_0 @ F @ E @ C @ B ) )
                      & ( r2_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) @ ( k1_toler_1 @ ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ( ( u1_waybel_0 @ A @ D )
                        = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X22: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( v6_waybel_0 @ X17 @ X16 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( X17
       != ( k4_waybel_9 @ X16 @ X15 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X22 @ X18 @ X15 ) @ X22 @ X18 @ X15 )
      | ~ ( r2_hidden @ X22 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X15: $i,X16: $i,X18: $i,X22: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_hidden @ X22 @ ( u1_struct_0 @ ( k4_waybel_9 @ X16 @ X15 @ X18 ) ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X22 @ X18 @ X15 ) @ X22 @ X18 @ X15 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X16 @ X15 @ X18 ) @ X16 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X16 @ X15 @ X18 ) @ X16 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) ) @ X3 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) @ X2 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X3 @ ( u1_struct_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) ) ) @ X0 @ X1 ) @ ( sk_C @ X3 @ ( u1_struct_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) ) ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( l1_waybel_0 @ ( k4_waybel_9 @ X24 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12 = X13 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
        = ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','29','30'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('50',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( l1_orders_2 @ X8 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('57',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['54','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4D9Ot8tw0l
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 48 iterations in 0.042s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.20/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.20/0.49  thf(k1_toler_1_type, type, k1_toler_1: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k4_waybel_9_type, type, k4_waybel_9: $i > $i > $i > $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(dt_l1_orders_2, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('0', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.49  thf(t13_waybel_9, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49               ( r1_tarski @
% 0.20/0.49                 ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.20/0.49                 ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                  ( r1_tarski @
% 0.20/0.49                    ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.20/0.49                    ( u1_struct_0 @ B ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t13_waybel_9])).
% 0.20/0.49  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k4_waybel_9, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.49         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.49       ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) & 
% 0.20/0.49         ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (l1_waybel_0 @ X23 @ X24)
% 0.20/0.49          | (v2_struct_0 @ X23)
% 0.20/0.49          | ~ (l1_struct_0 @ X24)
% 0.20/0.49          | (v2_struct_0 @ X24)
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.20/0.49          | (v6_waybel_0 @ (k4_waybel_9 @ X24 @ X23 @ X25) @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v6_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_struct_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.49  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(d3_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X1 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf(d7_waybel_9, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( l1_struct_0 @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( l1_waybel_0 @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( l1_waybel_0 @ D @ A ) & ( v6_waybel_0 @ D @ A ) ) =>
% 0.20/0.49                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.20/0.49                     ( ( ( u1_waybel_0 @ A @ D ) =
% 0.20/0.49                         ( k2_partfun1 @
% 0.20/0.49                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.49                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.20/0.49                       ( r2_relset_1 @
% 0.20/0.49                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.20/0.49                         ( u1_orders_2 @ D ) @ 
% 0.20/0.49                         ( k1_toler_1 @
% 0.20/0.49                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.20/0.49                       ( ![E:$i]:
% 0.20/0.49                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.20/0.49                           ( ?[F:$i]:
% 0.20/0.49                             ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.49                               ( ( F ) = ( E ) ) & ( r1_orders_2 @ B @ C @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_2, axiom,
% 0.20/0.49    (![F:$i,E:$i,C:$i,B:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ F @ E @ C @ B ) <=>
% 0.20/0.49       ( ( r1_orders_2 @ B @ C @ F ) & ( ( F ) = ( E ) ) & 
% 0.20/0.49         ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( v6_waybel_0 @ D @ A ) & ( l1_waybel_0 @ D @ A ) ) =>
% 0.20/0.49                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.20/0.49                     ( ( ![E:$i]:
% 0.20/0.49                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.20/0.49                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B ) ) ) ) & 
% 0.20/0.49                       ( r2_relset_1 @
% 0.20/0.49                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.20/0.49                         ( u1_orders_2 @ D ) @ 
% 0.20/0.49                         ( k1_toler_1 @
% 0.20/0.49                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.20/0.49                       ( ( u1_waybel_0 @ A @ D ) =
% 0.20/0.49                         ( k2_partfun1 @
% 0.20/0.49                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.49                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X22 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X15)
% 0.20/0.49          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.20/0.49          | ~ (v6_waybel_0 @ X17 @ X16)
% 0.20/0.49          | ~ (l1_waybel_0 @ X17 @ X16)
% 0.20/0.49          | ((X17) != (k4_waybel_9 @ X16 @ X15 @ X18))
% 0.20/0.49          | (zip_tseitin_0 @ (sk_F_1 @ X22 @ X18 @ X15) @ X22 @ X18 @ X15)
% 0.20/0.49          | ~ (r2_hidden @ X22 @ (u1_struct_0 @ X17))
% 0.20/0.49          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.20/0.49          | ~ (l1_struct_0 @ X16)
% 0.20/0.49          | (v2_struct_0 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X18 : $i, X22 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X16)
% 0.20/0.49          | ~ (l1_struct_0 @ X16)
% 0.20/0.49          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.20/0.49          | ~ (r2_hidden @ X22 @ 
% 0.20/0.49               (u1_struct_0 @ (k4_waybel_9 @ X16 @ X15 @ X18)))
% 0.20/0.49          | (zip_tseitin_0 @ (sk_F_1 @ X22 @ X18 @ X15) @ X22 @ X18 @ X15)
% 0.20/0.49          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X16 @ X15 @ X18) @ X16)
% 0.20/0.49          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X16 @ X15 @ X18) @ X16)
% 0.20/0.49          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.20/0.49          | (v2_struct_0 @ X15))),
% 0.20/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0)) @ X3)
% 0.20/0.49          | (v2_struct_0 @ X1)
% 0.20/0.49          | ~ (l1_waybel_0 @ X1 @ X2)
% 0.20/0.49          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X2 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X2 @ X1 @ X0) @ X2)
% 0.20/0.49          | (zip_tseitin_0 @ 
% 0.20/0.49             (sk_F_1 @ 
% 0.20/0.49              (sk_C @ X3 @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0))) @ 
% 0.20/0.49              X0 @ X1) @ 
% 0.20/0.49             (sk_C @ X3 @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0))) @ X0 @ 
% 0.20/0.49             X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.49          | ~ (l1_struct_0 @ X2)
% 0.20/0.49          | (v2_struct_0 @ X2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (zip_tseitin_0 @ 
% 0.20/0.49             (sk_F_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49              sk_C_1 @ sk_B) @ 
% 0.20/0.49             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49             sk_C_1 @ sk_B)
% 0.20/0.49          | ~ (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.20/0.49          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '15'])).
% 0.20/0.49  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (l1_waybel_0 @ X23 @ X24)
% 0.20/0.49          | (v2_struct_0 @ X23)
% 0.20/0.49          | ~ (l1_struct_0 @ X24)
% 0.20/0.49          | (v2_struct_0 @ X24)
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.20/0.49          | (l1_waybel_0 @ (k4_waybel_9 @ X24 @ X23 @ X25) @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_struct_0 @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.49  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.20/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (zip_tseitin_0 @ 
% 0.20/0.49             (sk_F_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49              sk_C_1 @ sk_B) @ 
% 0.20/0.49             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49             sk_C_1 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17', '18', '29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (((X12) = (X13)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X11 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.49           X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ((sk_F_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49              sk_C_1 @ sk_B)
% 0.20/0.49              = (sk_C @ X0 @ 
% 0.20/0.49                 (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (zip_tseitin_0 @ 
% 0.20/0.49             (sk_F_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49              sk_C_1 @ sk_B) @ 
% 0.20/0.49             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49             sk_C_1 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17', '18', '29', '30'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X12 @ X13 @ X11 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.49           X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (m1_subset_1 @ 
% 0.20/0.49             (sk_F_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49              sk_C_1 @ sk_B) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf(t2_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         ((r2_hidden @ X4 @ X5)
% 0.20/0.49          | (v1_xboole_0 @ X5)
% 0.20/0.49          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (sk_F_1 @ 
% 0.20/0.49              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49              sk_C_1 @ sk_B) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ 
% 0.20/0.49           (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49           (u1_struct_0 @ sk_B))
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.20/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['33', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49          | (r1_tarski @ 
% 0.20/0.49             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_B)
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.49             (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X1 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.49           (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.49           (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.49        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.49           (u1_struct_0 @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (~ (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.49          (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf(fc2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X6 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.20/0.49          | ~ (l1_struct_0 @ X6)
% 0.20/0.49          | (v2_struct_0 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('51', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, (~ (l1_struct_0 @ sk_B)),
% 0.20/0.49      inference('clc', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain, (~ (l1_orders_2 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '53'])).
% 0.20/0.49  thf('55', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_waybel_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) =>
% 0.20/0.49       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (l1_waybel_0 @ X8 @ X9) | (l1_orders_2 @ X8) | ~ (l1_struct_0 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.49  thf('57', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('59', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain, ($false), inference('demod', [status(thm)], ['54', '59'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
