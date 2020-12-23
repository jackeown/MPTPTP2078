%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EPe5RHneKw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:16 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  149 (1130 expanded)
%              Number of leaves         :   32 ( 332 expanded)
%              Depth                    :   23
%              Number of atoms          : 1107 (20653 expanded)
%              Number of equality atoms :   32 ( 104 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

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

thf('50',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
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

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r1_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['49','61'])).

thf('63',plain,
    ( ~ ( r1_xboole_0 @ sk_C @ k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','62'])).

thf('64',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','70'])).

thf('72',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','71','72'])).

thf('74',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','73'])).

thf('75',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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

thf('78',plain,(
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

thf('79',plain,(
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
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( m1_orders_2 @ sk_D @ sk_A @ X0 )
      | ( sk_D = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_C )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['75','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_D = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('99',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','71'])).

thf('100',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_C ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('104',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','71','72'])).

thf('108',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_D = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['101','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    sk_D = sk_C ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['74','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('114',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    $false ),
    inference('sup-',[status(thm)],['112','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EPe5RHneKw
% 0.12/0.35  % Computer   : n013.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 12:29:25 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 113 iterations in 0.053s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.35/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.35/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.35/0.54  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.35/0.54  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.35/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.35/0.54  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.35/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.54  thf(t84_orders_2, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.54               ( ![D:$i]:
% 0.35/0.54                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.35/0.54                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.54            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54              ( ![C:$i]:
% 0.35/0.54                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.54                  ( ![D:$i]:
% 0.35/0.54                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.35/0.54                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.35/0.54      inference('split', [status(esa)], ['2'])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.35/0.54         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(dt_m2_orders_2, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.35/0.54         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54       ( ![C:$i]:
% 0.35/0.54         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.54           ( ( v6_orders_2 @ C @ A ) & 
% 0.35/0.54             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.54         (~ (l1_orders_2 @ X14)
% 0.35/0.54          | ~ (v5_orders_2 @ X14)
% 0.35/0.54          | ~ (v4_orders_2 @ X14)
% 0.35/0.54          | ~ (v3_orders_2 @ X14)
% 0.35/0.54          | (v2_struct_0 @ X14)
% 0.35/0.54          | ~ (m1_orders_1 @ X15 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.35/0.54          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.54          | ~ (m2_orders_2 @ X16 @ X14 @ X15))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | (v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.54          | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.54          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.35/0.54  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.35/0.54      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '15'])).
% 0.35/0.54  thf(t67_orders_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.35/0.54          | (r1_tarski @ X19 @ X17)
% 0.35/0.54          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 0.35/0.54          | ~ (l1_orders_2 @ X18)
% 0.35/0.54          | ~ (v5_orders_2 @ X18)
% 0.35/0.54          | ~ (v4_orders_2 @ X18)
% 0.35/0.54          | ~ (v3_orders_2 @ X18)
% 0.35/0.54          | (v2_struct_0 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.35/0.54          | (r1_tarski @ X0 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.35/0.54          | (r1_tarski @ X0 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.35/0.54  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.35/0.54      inference('clc', [status(thm)], ['23', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '25'])).
% 0.35/0.54  thf(d8_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.35/0.54       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X0 : $i, X2 : $i]:
% 0.35/0.54         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.35/0.54         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.35/0.54      inference('split', [status(esa)], ['2'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      ((((sk_C) = (sk_D)))
% 0.35/0.54         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.35/0.54             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.35/0.54         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.35/0.54         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.35/0.54             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['30', '31'])).
% 0.35/0.54  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.37/0.54      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.54  thf(t69_orders_2, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54           ( ![C:$i]:
% 0.37/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.54          | ((X20) = (k1_xboole_0))
% 0.37/0.54          | ~ (m1_orders_2 @ X22 @ X21 @ X20)
% 0.37/0.54          | ~ (m1_orders_2 @ X20 @ X21 @ X22)
% 0.37/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.54          | ~ (l1_orders_2 @ X21)
% 0.37/0.54          | ~ (v5_orders_2 @ X21)
% 0.37/0.54          | ~ (v4_orders_2 @ X21)
% 0.37/0.54          | ~ (v3_orders_2 @ X21)
% 0.37/0.54          | (v2_struct_0 @ X21))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.54          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.37/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.54          | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.54  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.54          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.37/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.54          | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      ((((sk_C) = (k1_xboole_0))
% 0.37/0.54        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.37/0.54        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.37/0.54        | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['35', '43'])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.37/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.54  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('47', plain,
% 0.37/0.54      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.37/0.54      inference('clc', [status(thm)], ['45', '46'])).
% 0.37/0.54  thf('48', plain,
% 0.37/0.54      ((((sk_C) = (k1_xboole_0)))
% 0.37/0.54         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.37/0.54             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['32', '47'])).
% 0.37/0.54  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('50', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('51', plain,
% 0.37/0.54      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t82_orders_2, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54           ( ![C:$i]:
% 0.37/0.54             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.37/0.54               ( ![D:$i]:
% 0.37/0.54                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('52', plain,
% 0.37/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.54         (~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X24)))
% 0.37/0.54          | ~ (m2_orders_2 @ X25 @ X24 @ X23)
% 0.37/0.54          | ~ (r1_xboole_0 @ X26 @ X25)
% 0.37/0.54          | ~ (m2_orders_2 @ X26 @ X24 @ X23)
% 0.37/0.54          | ~ (l1_orders_2 @ X24)
% 0.37/0.54          | ~ (v5_orders_2 @ X24)
% 0.37/0.54          | ~ (v4_orders_2 @ X24)
% 0.37/0.54          | ~ (v3_orders_2 @ X24)
% 0.37/0.54          | (v2_struct_0 @ X24))),
% 0.37/0.54      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.37/0.54  thf('53', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.54          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.37/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.37/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.54  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('55', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('56', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('58', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.54          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.37/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.37/0.54      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.37/0.54  thf('59', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.54          | ~ (r1_xboole_0 @ sk_C @ X0)
% 0.37/0.54          | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['50', '58'])).
% 0.37/0.54  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('61', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ sk_C @ X0) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.37/0.54      inference('clc', [status(thm)], ['59', '60'])).
% 0.37/0.54  thf('62', plain, (~ (r1_xboole_0 @ sk_C @ sk_C)),
% 0.37/0.54      inference('sup-', [status(thm)], ['49', '61'])).
% 0.37/0.54  thf('63', plain,
% 0.37/0.54      ((~ (r1_xboole_0 @ sk_C @ k1_xboole_0))
% 0.37/0.54         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.37/0.54             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['48', '62'])).
% 0.37/0.54  thf('64', plain,
% 0.37/0.54      ((((sk_C) = (k1_xboole_0)))
% 0.37/0.54         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.37/0.54             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['32', '47'])).
% 0.37/0.54  thf(d10_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.54  thf('65', plain,
% 0.37/0.54      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.37/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.54  thf('66', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.37/0.54      inference('simplify', [status(thm)], ['65'])).
% 0.37/0.54  thf(l32_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.54  thf('67', plain,
% 0.37/0.54      (![X6 : $i, X8 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.37/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.54  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.54  thf(t79_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.37/0.54  thf('69', plain,
% 0.37/0.54      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.37/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.54  thf('70', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.54      inference('sup+', [status(thm)], ['68', '69'])).
% 0.37/0.54  thf('71', plain,
% 0.37/0.54      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.37/0.54      inference('demod', [status(thm)], ['63', '64', '70'])).
% 0.37/0.54  thf('72', plain,
% 0.37/0.54      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.37/0.54      inference('split', [status(esa)], ['0'])).
% 0.37/0.54  thf('73', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['3', '71', '72'])).
% 0.37/0.54  thf('74', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['1', '73'])).
% 0.37/0.54  thf('75', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('76', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('77', plain,
% 0.37/0.54      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t83_orders_2, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.54           ( ![C:$i]:
% 0.37/0.54             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.37/0.54               ( ![D:$i]:
% 0.37/0.54                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.37/0.54                   ( ( ( C ) != ( D ) ) =>
% 0.37/0.54                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.37/0.54                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('78', plain,
% 0.37/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.54         (~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X28)))
% 0.37/0.54          | ~ (m2_orders_2 @ X29 @ X28 @ X27)
% 0.37/0.54          | (m1_orders_2 @ X29 @ X28 @ X30)
% 0.37/0.54          | (m1_orders_2 @ X30 @ X28 @ X29)
% 0.37/0.54          | ((X30) = (X29))
% 0.37/0.54          | ~ (m2_orders_2 @ X30 @ X28 @ X27)
% 0.37/0.54          | ~ (l1_orders_2 @ X28)
% 0.37/0.54          | ~ (v5_orders_2 @ X28)
% 0.37/0.54          | ~ (v4_orders_2 @ X28)
% 0.37/0.54          | ~ (v3_orders_2 @ X28)
% 0.37/0.54          | (v2_struct_0 @ X28))),
% 0.37/0.54      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.37/0.54  thf('79', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.54          | ((X0) = (X1))
% 0.37/0.54          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.37/0.54          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.37/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.37/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.54  thf('80', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('81', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('82', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('84', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.54          | ((X0) = (X1))
% 0.37/0.54          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.37/0.54          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.37/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.37/0.54      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.37/0.54  thf('85', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.54          | (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.37/0.54          | (m1_orders_2 @ sk_D @ sk_A @ X0)
% 0.37/0.54          | ((sk_D) = (X0))
% 0.37/0.54          | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['76', '84'])).
% 0.37/0.54  thf('86', plain,
% 0.37/0.54      (((v2_struct_0 @ sk_A)
% 0.37/0.54        | ((sk_D) = (sk_C))
% 0.37/0.54        | (m1_orders_2 @ sk_D @ sk_A @ sk_C)
% 0.37/0.54        | (m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.37/0.54      inference('sup-', [status(thm)], ['75', '85'])).
% 0.37/0.54  thf('87', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.54  thf('88', plain,
% 0.37/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.54          | (r1_tarski @ X19 @ X17)
% 0.37/0.54          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 0.37/0.54          | ~ (l1_orders_2 @ X18)
% 0.37/0.54          | ~ (v5_orders_2 @ X18)
% 0.37/0.54          | ~ (v4_orders_2 @ X18)
% 0.37/0.54          | ~ (v3_orders_2 @ X18)
% 0.37/0.54          | (v2_struct_0 @ X18))),
% 0.37/0.54      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.37/0.54  thf('89', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.54          | (r1_tarski @ X0 @ sk_C))),
% 0.37/0.54      inference('sup-', [status(thm)], ['87', '88'])).
% 0.37/0.54  thf('90', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('91', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('92', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('93', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('94', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v2_struct_0 @ sk_A)
% 0.37/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.54          | (r1_tarski @ X0 @ sk_C))),
% 0.37/0.54      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.37/0.54  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('96', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.37/0.54      inference('clc', [status(thm)], ['94', '95'])).
% 0.37/0.54  thf('97', plain,
% 0.37/0.54      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.37/0.54        | ((sk_D) = (sk_C))
% 0.37/0.54        | (v2_struct_0 @ sk_A)
% 0.37/0.54        | (r1_tarski @ sk_D @ sk_C))),
% 0.37/0.54      inference('sup-', [status(thm)], ['86', '96'])).
% 0.37/0.54  thf('98', plain,
% 0.37/0.54      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.37/0.54         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.54      inference('split', [status(esa)], ['2'])).
% 0.37/0.54  thf('99', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['3', '71'])).
% 0.37/0.54  thf('100', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['98', '99'])).
% 0.37/0.54  thf('101', plain,
% 0.37/0.54      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_D) = (sk_C)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['97', '100'])).
% 0.37/0.54  thf('102', plain,
% 0.37/0.54      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.54      inference('split', [status(esa)], ['0'])).
% 0.37/0.54  thf('103', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.54  thf('104', plain,
% 0.37/0.54      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['102', '103'])).
% 0.37/0.54  thf('105', plain,
% 0.37/0.54      (![X3 : $i, X5 : $i]:
% 0.37/0.54         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.54  thf('106', plain,
% 0.37/0.54      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.37/0.54         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['104', '105'])).
% 0.37/0.54  thf('107', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['3', '71', '72'])).
% 0.37/0.54  thf('108', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['106', '107'])).
% 0.37/0.54  thf('109', plain, ((((sk_D) = (sk_C)) | (v2_struct_0 @ sk_A))),
% 0.37/0.54      inference('clc', [status(thm)], ['101', '108'])).
% 0.37/0.54  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('111', plain, (((sk_D) = (sk_C))),
% 0.37/0.54      inference('clc', [status(thm)], ['109', '110'])).
% 0.37/0.54  thf('112', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.37/0.54      inference('demod', [status(thm)], ['74', '111'])).
% 0.37/0.54  thf('113', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.54  thf('114', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.37/0.54      inference('simplify', [status(thm)], ['113'])).
% 0.37/0.54  thf('115', plain, ($false), inference('sup-', [status(thm)], ['112', '114'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
