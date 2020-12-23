%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qv83x5CDOn

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  148 (1133 expanded)
%              Number of leaves         :   32 ( 332 expanded)
%              Depth                    :   26
%              Number of atoms          : 1126 (20752 expanded)
%              Number of equality atoms :   30 ( 101 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('61',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['62'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_xboole_0 @ X8 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['61','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ! [X0: $i] :
        ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['50','69'])).

thf('71',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','70','71'])).

thf('73',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','72'])).

thf('74',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
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

thf('77',plain,(
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

thf('78',plain,(
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
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['85','95'])).

thf('97',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','70'])).

thf('99',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('103',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','70','71'])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['100','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['73','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('113',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    $false ),
    inference('sup-',[status(thm)],['111','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qv83x5CDOn
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 131 iterations in 0.054s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.22/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.22/0.52  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.52  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.22/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.52  thf(t84_orders_2, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.22/0.52                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.22/0.52                  ( ![D:$i]:
% 0.22/0.52                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.22/0.52                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.22/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_m2_orders_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.22/0.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.22/0.52           ( ( v6_orders_2 @ C @ A ) & 
% 0.22/0.52             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X14)
% 0.22/0.52          | ~ (v5_orders_2 @ X14)
% 0.22/0.52          | ~ (v4_orders_2 @ X14)
% 0.22/0.52          | ~ (v3_orders_2 @ X14)
% 0.22/0.52          | (v2_struct_0 @ X14)
% 0.22/0.52          | ~ (m1_orders_1 @ X15 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.22/0.52          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.52          | ~ (m2_orders_2 @ X16 @ X14 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.22/0.52  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '15'])).
% 0.22/0.52  thf(t67_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.52          | (r1_tarski @ X19 @ X17)
% 0.22/0.52          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 0.22/0.52          | ~ (l1_orders_2 @ X18)
% 0.22/0.52          | ~ (v5_orders_2 @ X18)
% 0.22/0.52          | ~ (v4_orders_2 @ X18)
% 0.22/0.52          | ~ (v3_orders_2 @ X18)
% 0.22/0.52          | (v2_struct_0 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.22/0.52          | (r1_tarski @ X0 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.22/0.52          | (r1_tarski @ X0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.22/0.52  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.22/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '25'])).
% 0.22/0.52  thf(d8_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.22/0.52       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i]:
% 0.22/0.52         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.22/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((((sk_C) = (sk_D)))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.22/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf(t69_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.22/0.52          | ((X20) = (k1_xboole_0))
% 0.22/0.52          | ~ (m1_orders_2 @ X22 @ X21 @ X20)
% 0.22/0.52          | ~ (m1_orders_2 @ X20 @ X21 @ X22)
% 0.22/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.22/0.52          | ~ (l1_orders_2 @ X21)
% 0.22/0.52          | ~ (v5_orders_2 @ X21)
% 0.22/0.52          | ~ (v4_orders_2 @ X21)
% 0.22/0.52          | ~ (v3_orders_2 @ X21)
% 0.22/0.52          | (v2_struct_0 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.22/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.22/0.52          | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.22/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.22/0.52          | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0))
% 0.22/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.22/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.22/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.52  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0)))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '47'])).
% 0.22/0.52  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t82_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.52         (~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X24)))
% 0.22/0.52          | ~ (m2_orders_2 @ X25 @ X24 @ X23)
% 0.22/0.52          | ~ (r1_xboole_0 @ X26 @ X25)
% 0.22/0.52          | ~ (m2_orders_2 @ X26 @ X24 @ X23)
% 0.22/0.52          | ~ (l1_orders_2 @ X24)
% 0.22/0.52          | ~ (v5_orders_2 @ X24)
% 0.22/0.52          | ~ (v4_orders_2 @ X24)
% 0.22/0.52          | ~ (v3_orders_2 @ X24)
% 0.22/0.52          | (v2_struct_0 @ X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('56', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52           | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52           | (v2_struct_0 @ sk_A)))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['51', '59'])).
% 0.22/0.52  thf(t3_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('61', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('63', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.22/0.52      inference('simplify', [status(thm)], ['62'])).
% 0.22/0.52  thf(t85_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X8 @ X9)
% 0.22/0.52          | (r1_xboole_0 @ X8 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.52  thf('66', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.52      inference('sup+', [status(thm)], ['61', '65'])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      ((![X0 : $i]: (~ (m2_orders_2 @ X0 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['60', '66'])).
% 0.22/0.52  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      ((![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))
% 0.22/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.22/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('clc', [status(thm)], ['67', '68'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['50', '69'])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('72', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['3', '70', '71'])).
% 0.22/0.52  thf('73', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['1', '72'])).
% 0.22/0.52  thf('74', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('75', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t83_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.22/0.52                   ( ( ( C ) != ( D ) ) =>
% 0.22/0.52                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.22/0.52                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.52         (~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X28)))
% 0.22/0.52          | ~ (m2_orders_2 @ X29 @ X28 @ X27)
% 0.22/0.52          | (m1_orders_2 @ X29 @ X28 @ X30)
% 0.22/0.52          | (m1_orders_2 @ X30 @ X28 @ X29)
% 0.22/0.52          | ((X30) = (X29))
% 0.22/0.52          | ~ (m2_orders_2 @ X30 @ X28 @ X27)
% 0.22/0.52          | ~ (l1_orders_2 @ X28)
% 0.22/0.52          | ~ (v5_orders_2 @ X28)
% 0.22/0.52          | ~ (v4_orders_2 @ X28)
% 0.22/0.52          | ~ (v3_orders_2 @ X28)
% 0.22/0.52          | (v2_struct_0 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52          | ((X0) = (X1))
% 0.22/0.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.22/0.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.22/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.52  thf('79', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('80', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('81', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52          | ((X0) = (X1))
% 0.22/0.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.22/0.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.22/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.52          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.22/0.52          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.22/0.52          | ((sk_C) = (X0))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['75', '83'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((sk_C) = (sk_D))
% 0.22/0.52        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.22/0.52        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['74', '84'])).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('87', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.52          | (r1_tarski @ X19 @ X17)
% 0.22/0.52          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 0.22/0.52          | ~ (l1_orders_2 @ X18)
% 0.22/0.52          | ~ (v5_orders_2 @ X18)
% 0.22/0.52          | ~ (v4_orders_2 @ X18)
% 0.22/0.52          | ~ (v3_orders_2 @ X18)
% 0.22/0.52          | (v2_struct_0 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.22/0.52          | (r1_tarski @ X0 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.52  thf('89', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('90', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('91', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.22/0.52          | (r1_tarski @ X0 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.22/0.52  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['93', '94'])).
% 0.22/0.52  thf('96', plain,
% 0.22/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.22/0.52        | ((sk_C) = (sk_D))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (r1_tarski @ sk_D @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['85', '95'])).
% 0.22/0.52  thf('97', plain,
% 0.22/0.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.22/0.52         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('98', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['3', '70'])).
% 0.22/0.52  thf('99', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 0.22/0.52  thf('100', plain,
% 0.22/0.52      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['96', '99'])).
% 0.22/0.52  thf('101', plain,
% 0.22/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('102', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.52  thf('103', plain,
% 0.22/0.52      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.52  thf('104', plain,
% 0.22/0.52      (![X3 : $i, X5 : $i]:
% 0.22/0.52         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('105', plain,
% 0.22/0.52      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.22/0.52         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['103', '104'])).
% 0.22/0.52  thf('106', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['3', '70', '71'])).
% 0.22/0.52  thf('107', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.22/0.52  thf('108', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['100', '107'])).
% 0.22/0.52  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('110', plain, (((sk_C) = (sk_D))),
% 0.22/0.52      inference('clc', [status(thm)], ['108', '109'])).
% 0.22/0.52  thf('111', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['73', '110'])).
% 0.22/0.52  thf('112', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.52  thf('113', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['112'])).
% 0.22/0.52  thf('114', plain, ($false), inference('sup-', [status(thm)], ['111', '113'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
