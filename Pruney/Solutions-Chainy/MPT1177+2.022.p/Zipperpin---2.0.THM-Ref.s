%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wKnuIYoPE

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 (1120 expanded)
%              Number of leaves         :   33 ( 329 expanded)
%              Depth                    :   26
%              Number of atoms          : 1108 (20668 expanded)
%              Number of equality atoms :   26 (  87 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t84_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( r2_xboole_0 @ C @ D )
                  <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_orders_2 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ B )
                   => ( ( r2_xboole_0 @ C @ D )
                    <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_orders_2])).

thf('0',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_orders_1 @ X15 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m2_orders_2 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_orders_2 @ X19 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,
    ( ( ( sk_C = sk_D )
      | ( r2_xboole_0 @ sk_C @ sk_D ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
   <= ~ ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( sk_C = sk_D )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t69_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( B != k1_xboole_0 )
                  & ( m1_orders_2 @ B @ A @ C )
                  & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_orders_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('52',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ~ ( r1_xboole_0 @ C @ D ) ) ) ) ) )).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_orders_1 @ X23 @ ( k1_orders_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m2_orders_2 @ X25 @ X24 @ X23 )
      | ~ ( r1_xboole_0 @ X26 @ X25 )
      | ~ ( m2_orders_2 @ X26 @ X24 @ X23 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
        | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('61',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X0: $i] :
        ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['50','66'])).

thf('68',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','67','68'])).

thf('70',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','69'])).

thf('71',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( C != D )
                   => ( ( m1_orders_2 @ C @ A @ D )
                    <=> ~ ( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m2_orders_2 @ X29 @ X28 @ X27 )
      | ( m1_orders_2 @ X29 @ X28 @ X30 )
      | ( m1_orders_2 @ X30 @ X28 @ X29 )
      | ( X30 = X29 )
      | ~ ( m2_orders_2 @ X30 @ X28 @ X27 )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('84',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_orders_2 @ X19 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('95',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','67'])).

thf('96',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('100',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('101',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','67','68'])).

thf('104',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['97','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['70','107'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('109',plain,(
    ! [X3: $i] :
      ~ ( r2_xboole_0 @ X3 @ X3 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('110',plain,(
    $false ),
    inference('sup-',[status(thm)],['108','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wKnuIYoPE
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 180 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.51  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.51  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(t84_orders_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.51                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.51                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.21/0.51         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m2_orders_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.51         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.51           ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.51             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X14)
% 0.21/0.51          | ~ (v5_orders_2 @ X14)
% 0.21/0.51          | ~ (v4_orders_2 @ X14)
% 0.21/0.51          | ~ (v3_orders_2 @ X14)
% 0.21/0.51          | (v2_struct_0 @ X14)
% 0.21/0.51          | ~ (m1_orders_1 @ X15 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.51          | ~ (m2_orders_2 @ X16 @ X14 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.21/0.51  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '15'])).
% 0.21/0.51  thf(t67_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | (r1_tarski @ X19 @ X17)
% 0.21/0.51          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 0.21/0.51          | ~ (l1_orders_2 @ X18)
% 0.21/0.51          | ~ (v5_orders_2 @ X18)
% 0.21/0.51          | ~ (v4_orders_2 @ X18)
% 0.21/0.51          | ~ (v3_orders_2 @ X18)
% 0.21/0.51          | (v2_struct_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.21/0.51          | (r1_tarski @ X0 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.21/0.51          | (r1_tarski @ X0 @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.21/0.51  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '25'])).
% 0.21/0.51  thf(d8_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i]:
% 0.21/0.51         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.21/0.51         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((((sk_C) = (sk_D)))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.21/0.51         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(t69_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ((X20) = (k1_xboole_0))
% 0.21/0.51          | ~ (m1_orders_2 @ X22 @ X21 @ X20)
% 0.21/0.51          | ~ (m1_orders_2 @ X20 @ X21 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ~ (l1_orders_2 @ X21)
% 0.21/0.51          | ~ (v5_orders_2 @ X21)
% 0.21/0.51          | ~ (v4_orders_2 @ X21)
% 0.21/0.51          | ~ (v3_orders_2 @ X21)
% 0.21/0.51          | (v2_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.21/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.51          | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.21/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.51          | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0))
% 0.21/0.51        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.21/0.51        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.21/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.51  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '47'])).
% 0.21/0.51  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t82_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.51         (~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X24)))
% 0.21/0.51          | ~ (m2_orders_2 @ X25 @ X24 @ X23)
% 0.21/0.51          | ~ (r1_xboole_0 @ X26 @ X25)
% 0.21/0.51          | ~ (m2_orders_2 @ X26 @ X24 @ X23)
% 0.21/0.51          | ~ (l1_orders_2 @ X24)
% 0.21/0.51          | ~ (v5_orders_2 @ X24)
% 0.21/0.51          | ~ (v4_orders_2 @ X24)
% 0.21/0.51          | ~ (v3_orders_2 @ X24)
% 0.21/0.51          | (v2_struct_0 @ X24))),
% 0.21/0.51      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51           | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.51           | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '59'])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('61', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf(t106_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.51       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X7 @ X9)
% 0.21/0.51          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.21/0.51  thf('63', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((![X0 : $i]: (~ (m2_orders_2 @ X0 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['60', '63'])).
% 0.21/0.51  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))
% 0.21/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('69', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['3', '67', '68'])).
% 0.21/0.51  thf('70', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['1', '69'])).
% 0.21/0.51  thf('71', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('72', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t83_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.51                   ( ( ( C ) != ( D ) ) =>
% 0.21/0.51                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.21/0.51                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         (~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X28)))
% 0.21/0.51          | ~ (m2_orders_2 @ X29 @ X28 @ X27)
% 0.21/0.51          | (m1_orders_2 @ X29 @ X28 @ X30)
% 0.21/0.51          | (m1_orders_2 @ X30 @ X28 @ X29)
% 0.21/0.51          | ((X30) = (X29))
% 0.21/0.51          | ~ (m2_orders_2 @ X30 @ X28 @ X27)
% 0.21/0.51          | ~ (l1_orders_2 @ X28)
% 0.21/0.51          | ~ (v5_orders_2 @ X28)
% 0.21/0.51          | ~ (v4_orders_2 @ X28)
% 0.21/0.51          | ~ (v3_orders_2 @ X28)
% 0.21/0.51          | (v2_struct_0 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.51          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.51          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('77', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('78', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.51          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.51          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.51          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.51          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.21/0.51          | ((sk_C) = (X0))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((sk_C) = (sk_D))
% 0.21/0.51        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.21/0.51        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '81'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | (r1_tarski @ X19 @ X17)
% 0.21/0.51          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 0.21/0.51          | ~ (l1_orders_2 @ X18)
% 0.21/0.51          | ~ (v5_orders_2 @ X18)
% 0.21/0.51          | ~ (v4_orders_2 @ X18)
% 0.21/0.51          | ~ (v3_orders_2 @ X18)
% 0.21/0.51          | (v2_struct_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.51          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.51          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.21/0.51  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['90', '91'])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.21/0.51        | ((sk_C) = (sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (r1_tarski @ sk_D @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['82', '92'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.21/0.51         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['2'])).
% 0.21/0.51  thf('95', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['3', '67'])).
% 0.21/0.51  thf('96', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['93', '96'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.21/0.51         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.51  thf('103', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['3', '67', '68'])).
% 0.21/0.51  thf('104', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 0.21/0.51  thf('105', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['97', '104'])).
% 0.21/0.51  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('107', plain, (((sk_C) = (sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['105', '106'])).
% 0.21/0.51  thf('108', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['70', '107'])).
% 0.21/0.51  thf(irreflexivity_r2_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.21/0.51  thf('109', plain, (![X3 : $i]: ~ (r2_xboole_0 @ X3 @ X3)),
% 0.21/0.51      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.21/0.51  thf('110', plain, ($false), inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
