%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jTaYeQKdC7

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:21 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 476 expanded)
%              Number of leaves         :   32 ( 146 expanded)
%              Depth                    :   25
%              Number of atoms          : 2369 (8352 expanded)
%              Number of equality atoms :   26 ( 218 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(a_3_0_waybel_9_type,type,(
    a_3_0_waybel_9: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t12_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) )
                = ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) )
                  = ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_waybel_9])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ( v6_waybel_0 @ ( k4_waybel_9 @ X21 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
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

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X19: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v6_waybel_0 @ X14 @ X13 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( X14
       != ( k4_waybel_9 @ X13 @ X12 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X15 @ X12 ) @ X19 @ X15 @ X12 )
      | ~ ( r2_hidden @ X19 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X15: $i,X19: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ X19 @ ( u1_struct_0 @ ( k4_waybel_9 @ X13 @ X12 @ X15 ) ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X15 @ X12 ) @ X19 @ X15 @ X12 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X13 @ X12 @ X15 ) @ X13 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X13 @ X12 @ X15 ) @ X13 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ( l1_waybel_0 @ ( k4_waybel_9 @ X21 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','30','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9 = X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
        = ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','30','31'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r1_orders_2 @ X7 @ X8 @ X9 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
        = ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','30','31'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fraenkel_a_3_0_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_struct_0 @ B )
        & ~ ( v2_struct_0 @ C )
        & ( l1_waybel_0 @ C @ B )
        & ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) )
     => ( ( r2_hidden @ A @ ( a_3_0_waybel_9 @ B @ C @ D ) )
      <=> ? [E: $i] :
            ( ( r1_orders_2 @ C @ D @ E )
            & ( A = E )
            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ X26 @ ( a_3_0_waybel_9 @ X24 @ X23 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X23 ) )
      | ( X26 != X27 )
      | ~ ( r1_orders_2 @ X23 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( r1_orders_2 @ X23 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ X27 @ ( a_3_0_waybel_9 @ X24 @ X23 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X1 @ sk_B @ X2 ) )
      | ~ ( r1_orders_2 @ sk_B @ X2 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_orders_2 @ sk_B @ X2 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X1 @ sk_B @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X1 @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( X26
        = ( sk_E_1 @ X25 @ X23 @ X26 ) )
      | ~ ( r2_hidden @ X26 @ ( a_3_0_waybel_9 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( X1
        = ( sk_E_1 @ sk_C_1 @ sk_B @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( r1_orders_2 @ X23 @ X25 @ ( sk_E_1 @ X25 @ X23 @ X26 ) )
      | ~ ( r2_hidden @ X26 @ ( a_3_0_waybel_9 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('82',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X25 @ X23 @ X26 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X26 @ ( a_3_0_waybel_9 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) @ X3 )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ X1 @ ( sk_C @ X3 @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X11 ) )
      | ( X9 != X10 )
      | ~ ( r1_orders_2 @ X11 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r1_orders_2 @ X11 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_B @ X1 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v6_waybel_0 @ X14 @ X13 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( X14
       != ( k4_waybel_9 @ X13 @ X12 @ X15 ) )
      | ( r2_hidden @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,(
    ! [X12: $i,X13: $i,X15: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X15 @ X12 )
      | ( r2_hidden @ X17 @ ( u1_struct_0 @ ( k4_waybel_9 @ X13 @ X12 @ X15 ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X13 @ X12 @ X15 ) @ X13 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X13 @ X12 @ X15 ) @ X13 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ sk_C_1 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('106',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('111',plain,
    ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('117',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
 != ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['60','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jTaYeQKdC7
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 227 iterations in 0.190s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.47/0.65  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.47/0.65  thf(a_3_0_waybel_9_type, type, a_3_0_waybel_9: $i > $i > $i > $i).
% 0.47/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.47/0.65  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.47/0.65  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.47/0.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.47/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.47/0.65  thf(k4_waybel_9_type, type, k4_waybel_9: $i > $i > $i > $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.47/0.65  thf(k1_toler_1_type, type, k1_toler_1: $i > $i > $i).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(t12_waybel_9, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.47/0.65               ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) =
% 0.47/0.65                 ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.66              ( ![C:$i]:
% 0.47/0.66                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.47/0.66                  ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) =
% 0.47/0.66                    ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t12_waybel_9])).
% 0.47/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('2', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(dt_k4_waybel_9, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.47/0.66         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.47/0.66         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.47/0.66       ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) & 
% 0.47/0.66         ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ))).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.66         (~ (l1_waybel_0 @ X20 @ X21)
% 0.47/0.66          | (v2_struct_0 @ X20)
% 0.47/0.66          | ~ (l1_struct_0 @ X21)
% 0.47/0.66          | (v2_struct_0 @ X21)
% 0.47/0.66          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.47/0.66          | (v6_waybel_0 @ (k4_waybel_9 @ X21 @ X20 @ X22) @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v6_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_B)
% 0.47/0.66        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '5'])).
% 0.47/0.66  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_B)
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      ((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf(d3_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf(d7_waybel_9, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( l1_struct_0 @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( l1_waybel_0 @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.47/0.66               ( ![D:$i]:
% 0.47/0.66                 ( ( ( l1_waybel_0 @ D @ A ) & ( v6_waybel_0 @ D @ A ) ) =>
% 0.47/0.66                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.47/0.66                     ( ( ( u1_waybel_0 @ A @ D ) =
% 0.47/0.66                         ( k2_partfun1 @
% 0.47/0.66                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.66                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.47/0.66                       ( r2_relset_1 @
% 0.47/0.66                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.47/0.66                         ( u1_orders_2 @ D ) @ 
% 0.47/0.66                         ( k1_toler_1 @
% 0.47/0.66                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.47/0.66                       ( ![E:$i]:
% 0.47/0.66                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.47/0.66                           ( ?[F:$i]:
% 0.47/0.66                             ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.66                               ( ( F ) = ( E ) ) & ( r1_orders_2 @ B @ C @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.47/0.66  thf(zf_stmt_2, axiom,
% 0.47/0.66    (![F:$i,E:$i,C:$i,B:$i]:
% 0.47/0.66     ( ( zip_tseitin_0 @ F @ E @ C @ B ) <=>
% 0.47/0.66       ( ( r1_orders_2 @ B @ C @ F ) & ( ( F ) = ( E ) ) & 
% 0.47/0.66         ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_3, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.66           ( ![C:$i]:
% 0.47/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.47/0.66               ( ![D:$i]:
% 0.47/0.66                 ( ( ( v6_waybel_0 @ D @ A ) & ( l1_waybel_0 @ D @ A ) ) =>
% 0.47/0.66                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.47/0.66                     ( ( ![E:$i]:
% 0.47/0.66                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.47/0.66                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B ) ) ) ) & 
% 0.47/0.66                       ( r2_relset_1 @
% 0.47/0.66                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.47/0.66                         ( u1_orders_2 @ D ) @ 
% 0.47/0.66                         ( k1_toler_1 @
% 0.47/0.66                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.47/0.66                       ( ( u1_waybel_0 @ A @ D ) =
% 0.47/0.66                         ( k2_partfun1 @
% 0.47/0.66                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.66                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X19 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X12)
% 0.47/0.66          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.47/0.66          | ~ (v6_waybel_0 @ X14 @ X13)
% 0.47/0.66          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.47/0.66          | ((X14) != (k4_waybel_9 @ X13 @ X12 @ X15))
% 0.47/0.66          | (zip_tseitin_0 @ (sk_F_1 @ X19 @ X15 @ X12) @ X19 @ X15 @ X12)
% 0.47/0.66          | ~ (r2_hidden @ X19 @ (u1_struct_0 @ X14))
% 0.47/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.47/0.66          | ~ (l1_struct_0 @ X13)
% 0.47/0.66          | (v2_struct_0 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i, X15 : $i, X19 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X13)
% 0.47/0.66          | ~ (l1_struct_0 @ X13)
% 0.47/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.47/0.66          | ~ (r2_hidden @ X19 @ 
% 0.47/0.66               (u1_struct_0 @ (k4_waybel_9 @ X13 @ X12 @ X15)))
% 0.47/0.66          | (zip_tseitin_0 @ (sk_F_1 @ X19 @ X15 @ X12) @ X19 @ X15 @ X12)
% 0.47/0.66          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X13 @ X12 @ X15) @ X13)
% 0.47/0.66          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X13 @ X12 @ X15) @ X13)
% 0.47/0.66          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.47/0.66          | (v2_struct_0 @ X12))),
% 0.47/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0)) @ X3)
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (l1_waybel_0 @ X1 @ X2)
% 0.47/0.66          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X2 @ X1 @ X0) @ X2)
% 0.47/0.66          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X2 @ X1 @ X0) @ X2)
% 0.47/0.66          | (zip_tseitin_0 @ 
% 0.47/0.66             (sk_F_1 @ 
% 0.47/0.66              (sk_C @ X3 @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0))) @ 
% 0.47/0.66              X0 @ X1) @ 
% 0.47/0.66             (sk_C @ X3 @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0))) @ X0 @ 
% 0.47/0.66             X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.47/0.66          | ~ (l1_struct_0 @ X2)
% 0.47/0.66          | (v2_struct_0 @ X2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '15'])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))
% 0.47/0.66          | (zip_tseitin_0 @ 
% 0.47/0.66             (sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B) @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             sk_C_1 @ sk_B)
% 0.47/0.66          | ~ (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '16'])).
% 0.47/0.66  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('19', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('20', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('21', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.66         (~ (l1_waybel_0 @ X20 @ X21)
% 0.47/0.66          | (v2_struct_0 @ X20)
% 0.47/0.66          | ~ (l1_struct_0 @ X21)
% 0.47/0.66          | (v2_struct_0 @ X21)
% 0.47/0.66          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.47/0.66          | (l1_waybel_0 @ (k4_waybel_9 @ X21 @ X20 @ X22) @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_B)
% 0.47/0.66        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '23'])).
% 0.47/0.66  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_B)
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('clc', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('31', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (zip_tseitin_0 @ 
% 0.47/0.66             (sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B) @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             sk_C_1 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18', '19', '30', '31'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         (((X9) = (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ((sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B)
% 0.47/0.66              = (sk_C @ X0 @ 
% 0.47/0.66                 (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (zip_tseitin_0 @ 
% 0.47/0.66             (sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B) @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             sk_C_1 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18', '19', '30', '31'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         ((r1_orders_2 @ X7 @ X8 @ X9) | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66             (sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66           (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['34', '37'])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ((sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B)
% 0.47/0.66              = (sk_C @ X0 @ 
% 0.47/0.66                 (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (zip_tseitin_0 @ 
% 0.47/0.66             (sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B) @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             sk_C_1 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18', '19', '30', '31'])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         ((m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.47/0.66          | ~ (zip_tseitin_0 @ X9 @ X10 @ X8 @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (sk_F_1 @ 
% 0.47/0.66              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66              sk_C_1 @ sk_B) @ 
% 0.47/0.66             (u1_struct_0 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((m1_subset_1 @ 
% 0.47/0.66           (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66           (u1_struct_0 @ sk_B))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['40', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (u1_struct_0 @ sk_B)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.66  thf(fraenkel_a_3_0_waybel_9, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) & 
% 0.47/0.66         ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ B ) & 
% 0.47/0.66         ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) ) =>
% 0.47/0.66       ( ( r2_hidden @ A @ ( a_3_0_waybel_9 @ B @ C @ D ) ) <=>
% 0.47/0.66         ( ?[E:$i]:
% 0.47/0.66           ( ( r1_orders_2 @ C @ D @ E ) & ( ( A ) = ( E ) ) & 
% 0.47/0.66             ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ))).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.66         (~ (l1_waybel_0 @ X23 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X23)
% 0.47/0.66          | ~ (l1_struct_0 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X24)
% 0.47/0.66          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.47/0.66          | (r2_hidden @ X26 @ (a_3_0_waybel_9 @ X24 @ X23 @ X25))
% 0.47/0.66          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X23))
% 0.47/0.66          | ((X26) != (X27))
% 0.47/0.66          | ~ (r1_orders_2 @ X23 @ X25 @ X27))),
% 0.47/0.66      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.47/0.66         (~ (r1_orders_2 @ X23 @ X25 @ X27)
% 0.47/0.66          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X23))
% 0.47/0.66          | (r2_hidden @ X27 @ (a_3_0_waybel_9 @ X24 @ X23 @ X25))
% 0.47/0.66          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.47/0.66          | (v2_struct_0 @ X24)
% 0.47/0.66          | ~ (l1_struct_0 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X23)
% 0.47/0.66          | ~ (l1_waybel_0 @ X23 @ X24))),
% 0.47/0.66      inference('simplify', [status(thm)], ['46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X1)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_struct_0 @ X1)
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B))
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (a_3_0_waybel_9 @ X1 @ sk_B @ X2))
% 0.47/0.66          | ~ (r1_orders_2 @ sk_B @ X2 @ 
% 0.47/0.66               (sk_C @ X0 @ 
% 0.47/0.66                (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['45', '47'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r1_orders_2 @ sk_B @ X2 @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (a_3_0_waybel_9 @ X1 @ sk_B @ X2))
% 0.47/0.66          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B))
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (l1_struct_0 @ X1)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X1)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X1)
% 0.47/0.66          | ~ (l1_struct_0 @ X1)
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (a_3_0_waybel_9 @ X1 @ sk_B @ sk_C_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['39', '49'])).
% 0.47/0.66  thf('51', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X1)
% 0.47/0.66          | ~ (l1_struct_0 @ X1)
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (a_3_0_waybel_9 @ X1 @ sk_B @ sk_C_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['50', '51'])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r2_hidden @ 
% 0.47/0.66           (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66           (a_3_0_waybel_9 @ X1 @ sk_B @ sk_C_1))
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (l1_struct_0 @ X1)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X1)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['52'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '53'])).
% 0.47/0.66  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_hidden @ 
% 0.47/0.66           (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66           (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66          | (r1_tarski @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['56'])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_B)
% 0.47/0.66        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['57', '58'])).
% 0.47/0.66  thf('60', plain,
% 0.47/0.66      (((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66         (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66        | (v2_struct_0 @ sk_B)
% 0.47/0.66        | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('simplify', [status(thm)], ['59'])).
% 0.47/0.66  thf('61', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('62', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('63', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.66         (~ (l1_waybel_0 @ X23 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X23)
% 0.47/0.66          | ~ (l1_struct_0 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X24)
% 0.47/0.66          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.47/0.66          | ((X26) = (sk_E_1 @ X25 @ X23 @ X26))
% 0.47/0.66          | ~ (r2_hidden @ X26 @ (a_3_0_waybel_9 @ X24 @ X23 @ X25)))),
% 0.47/0.66      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.47/0.66          | ((X1) = (sk_E_1 @ sk_C_1 @ sk_B @ X1))
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X1)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ((sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.47/0.66              = (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66                 (sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['62', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66            = (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['61', '66'])).
% 0.47/0.66  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66            = (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('72', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.66         (~ (l1_waybel_0 @ X23 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X23)
% 0.47/0.66          | ~ (l1_struct_0 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X24)
% 0.47/0.66          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.47/0.66          | (r1_orders_2 @ X23 @ X25 @ (sk_E_1 @ X25 @ X23 @ X26))
% 0.47/0.66          | ~ (r2_hidden @ X26 @ (a_3_0_waybel_9 @ X24 @ X23 @ X25)))),
% 0.47/0.66      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.47/0.66  thf('74', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.47/0.66          | (r1_orders_2 @ sk_B @ sk_C_1 @ (sk_E_1 @ sk_C_1 @ sk_B @ X1))
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X1)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | (r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66             (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66              (sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['71', '74'])).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66           (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66            (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['70', '75'])).
% 0.47/0.66  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66           (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66            (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.47/0.66  thf('79', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66           (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)))
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['69', '78'])).
% 0.47/0.66  thf('80', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (r1_orders_2 @ sk_B @ sk_C_1 @ 
% 0.47/0.66             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['79'])).
% 0.47/0.66  thf('81', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66            = (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('82', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('83', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('84', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.66         (~ (l1_waybel_0 @ X23 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X23)
% 0.47/0.66          | ~ (l1_struct_0 @ X24)
% 0.47/0.66          | (v2_struct_0 @ X24)
% 0.47/0.66          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.47/0.66          | (m1_subset_1 @ (sk_E_1 @ X25 @ X23 @ X26) @ (u1_struct_0 @ X23))
% 0.47/0.66          | ~ (r2_hidden @ X26 @ (a_3_0_waybel_9 @ X24 @ X23 @ X25)))),
% 0.47/0.66      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.47/0.66  thf('86', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ X2 @ X1 @ X0) @ X3)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (sk_E_1 @ X0 @ X1 @ (sk_C @ X3 @ (a_3_0_waybel_9 @ X2 @ X1 @ X0))) @ 
% 0.47/0.66             (u1_struct_0 @ X1))
% 0.47/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.47/0.66          | (v2_struct_0 @ X2)
% 0.47/0.66          | ~ (l1_struct_0 @ X2)
% 0.47/0.66          | (v2_struct_0 @ X1)
% 0.47/0.66          | ~ (l1_waybel_0 @ X1 @ X2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.66  thf('87', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (l1_waybel_0 @ sk_B @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66              (sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (u1_struct_0 @ sk_B))
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['83', '86'])).
% 0.47/0.66  thf('88', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66              (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (u1_struct_0 @ sk_B))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['82', '87'])).
% 0.47/0.66  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('90', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (sk_E_1 @ sk_C_1 @ sk_B @ 
% 0.47/0.66              (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.47/0.66             (u1_struct_0 @ sk_B))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['88', '89'])).
% 0.47/0.66  thf('91', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((m1_subset_1 @ 
% 0.47/0.66           (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           (u1_struct_0 @ sk_B))
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['81', '90'])).
% 0.47/0.66  thf('92', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (m1_subset_1 @ 
% 0.47/0.66             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66             (u1_struct_0 @ sk_B)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['91'])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.66         ((zip_tseitin_0 @ X9 @ X10 @ X8 @ X11)
% 0.47/0.66          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X11))
% 0.47/0.66          | ((X9) != (X10))
% 0.47/0.66          | ~ (r1_orders_2 @ X11 @ X8 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.66  thf('94', plain,
% 0.47/0.66      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.47/0.66         (~ (r1_orders_2 @ X11 @ X8 @ X10)
% 0.47/0.66          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.47/0.66          | (zip_tseitin_0 @ X10 @ X10 @ X8 @ X11))),
% 0.47/0.66      inference('simplify', [status(thm)], ['93'])).
% 0.47/0.66  thf('95', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (zip_tseitin_0 @ 
% 0.47/0.66             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X1 @ sk_B)
% 0.47/0.66          | ~ (r1_orders_2 @ sk_B @ X1 @ 
% 0.47/0.66               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['92', '94'])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (zip_tseitin_0 @ 
% 0.47/0.66             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.47/0.66             sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['80', '95'])).
% 0.47/0.66  thf('97', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((zip_tseitin_0 @ 
% 0.47/0.66           (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ sk_C_1 @ 
% 0.47/0.66           sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['96'])).
% 0.47/0.66  thf('98', plain,
% 0.47/0.66      ((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf('99', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('100', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X12)
% 0.47/0.66          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.47/0.66          | ~ (v6_waybel_0 @ X14 @ X13)
% 0.47/0.66          | ~ (l1_waybel_0 @ X14 @ X13)
% 0.47/0.66          | ((X14) != (k4_waybel_9 @ X13 @ X12 @ X15))
% 0.47/0.66          | (r2_hidden @ X17 @ (u1_struct_0 @ X14))
% 0.47/0.66          | ~ (zip_tseitin_0 @ X18 @ X17 @ X15 @ X12)
% 0.47/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.47/0.66          | ~ (l1_struct_0 @ X13)
% 0.47/0.66          | (v2_struct_0 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.66  thf('101', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.47/0.66         ((v2_struct_0 @ X13)
% 0.47/0.66          | ~ (l1_struct_0 @ X13)
% 0.47/0.66          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.47/0.66          | ~ (zip_tseitin_0 @ X18 @ X17 @ X15 @ X12)
% 0.47/0.66          | (r2_hidden @ X17 @ (u1_struct_0 @ (k4_waybel_9 @ X13 @ X12 @ X15)))
% 0.47/0.66          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X13 @ X12 @ X15) @ X13)
% 0.47/0.66          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X13 @ X12 @ X15) @ X13)
% 0.47/0.66          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.47/0.66          | (v2_struct_0 @ X12))),
% 0.47/0.66      inference('simplify', [status(thm)], ['100'])).
% 0.47/0.66  thf('102', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_B)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.47/0.66          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (r2_hidden @ X1 @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1)))
% 0.47/0.66          | ~ (zip_tseitin_0 @ X2 @ X1 @ sk_C_1 @ sk_B)
% 0.47/0.66          | ~ (l1_struct_0 @ X0)
% 0.47/0.66          | (v2_struct_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['99', '101'])).
% 0.47/0.66  thf('103', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B)
% 0.47/0.66          | (r2_hidden @ X0 @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))
% 0.47/0.66          | ~ (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.47/0.66          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['98', '102'])).
% 0.47/0.66  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('105', plain,
% 0.47/0.66      ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.47/0.66      inference('clc', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('106', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('107', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((v2_struct_0 @ sk_A)
% 0.47/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B)
% 0.47/0.66          | (r2_hidden @ X0 @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))
% 0.47/0.66          | (v2_struct_0 @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.47/0.66  thf('108', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r2_hidden @ 
% 0.47/0.66             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))
% 0.47/0.66          | (v2_struct_0 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['97', '107'])).
% 0.47/0.66  thf('109', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_hidden @ (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))
% 0.47/0.66          | (v2_struct_0 @ sk_A)
% 0.47/0.66          | (v2_struct_0 @ sk_B)
% 0.47/0.66          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['108'])).
% 0.47/0.66  thf('110', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('111', plain,
% 0.47/0.66      (((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.47/0.66         (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))
% 0.47/0.66        | (v2_struct_0 @ sk_B)
% 0.47/0.66        | (v2_struct_0 @ sk_A)
% 0.47/0.66        | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.47/0.66           (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['109', '110'])).
% 0.47/0.66  thf('112', plain,
% 0.47/0.66      (((v2_struct_0 @ sk_A)
% 0.47/0.66        | (v2_struct_0 @ sk_B)
% 0.47/0.66        | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.47/0.66           (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['111'])).
% 0.47/0.66  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('114', plain,
% 0.47/0.66      (((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.47/0.66         (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))
% 0.47/0.66        | (v2_struct_0 @ sk_B))),
% 0.47/0.66      inference('clc', [status(thm)], ['112', '113'])).
% 0.47/0.66  thf('115', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('116', plain,
% 0.47/0.66      ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.47/0.66        (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))),
% 0.47/0.66      inference('clc', [status(thm)], ['114', '115'])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('117', plain,
% 0.47/0.66      (![X4 : $i, X6 : $i]:
% 0.47/0.66         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('118', plain,
% 0.47/0.66      ((~ (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66           (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66        | ((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66            = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['116', '117'])).
% 0.47/0.66  thf('119', plain,
% 0.47/0.66      (((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.47/0.66         != (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('120', plain,
% 0.47/0.66      (~ (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.47/0.66          (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.47/0.66  thf('121', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.47/0.66      inference('clc', [status(thm)], ['60', '120'])).
% 0.47/0.66  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('123', plain, ((v2_struct_0 @ sk_B)),
% 0.47/0.66      inference('clc', [status(thm)], ['121', '122'])).
% 0.47/0.66  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
