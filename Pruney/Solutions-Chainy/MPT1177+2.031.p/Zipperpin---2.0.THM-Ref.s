%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O93SfnXTzp

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  151 (1142 expanded)
%              Number of leaves         :   32 ( 335 expanded)
%              Depth                    :   24
%              Number of atoms          : 1129 (20764 expanded)
%              Number of equality atoms :   32 ( 110 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_orders_1 @ X16 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m2_orders_2 @ X17 @ X15 @ X16 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ X20 @ X18 )
      | ~ ( m1_orders_2 @ X20 @ X19 @ X18 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( X21 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X23 @ X22 @ X21 )
      | ~ ( m1_orders_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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

thf('51',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_orders_1 @ X24 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m2_orders_2 @ X26 @ X25 @ X24 )
      | ~ ( r1_xboole_0 @ X27 @ X26 )
      | ~ ( m2_orders_2 @ X27 @ X25 @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_xboole_0 @ sk_C @ k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','62'])).

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

thf('69',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','72'])).

thf('74',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','73','74'])).

thf('76',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','75'])).

thf('77',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
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

thf('80',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_orders_1 @ X28 @ ( k1_orders_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m2_orders_2 @ X30 @ X29 @ X28 )
      | ( m1_orders_2 @ X30 @ X29 @ X31 )
      | ( m1_orders_2 @ X31 @ X29 @ X30 )
      | ( X31 = X30 )
      | ~ ( m2_orders_2 @ X31 @ X29 @ X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('81',plain,(
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
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( m1_orders_2 @ sk_D @ sk_A @ X0 )
      | ( sk_D = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_C )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ X20 @ X18 )
      | ~ ( m1_orders_2 @ X20 @ X19 @ X18 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_D = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['88','98'])).

thf('100',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','73'])).

thf('102',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_C ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('106',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','73','74'])).

thf('110',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_D = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    sk_D = sk_C ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['76','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('116',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    $false ),
    inference('sup-',[status(thm)],['114','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O93SfnXTzp
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:54:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 132 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.49  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(t84_orders_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.49                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.49                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.49         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_m2_orders_2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.49           ( ( v6_orders_2 @ C @ A ) & 
% 0.20/0.49             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (l1_orders_2 @ X15)
% 0.20/0.49          | ~ (v5_orders_2 @ X15)
% 0.20/0.49          | ~ (v4_orders_2 @ X15)
% 0.20/0.49          | ~ (v3_orders_2 @ X15)
% 0.20/0.49          | (v2_struct_0 @ X15)
% 0.20/0.49          | ~ (m1_orders_1 @ X16 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.20/0.49          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.49          | ~ (m2_orders_2 @ X17 @ X15 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.49  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '15'])).
% 0.20/0.49  thf(t67_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.49          | (r1_tarski @ X20 @ X18)
% 0.20/0.49          | ~ (m1_orders_2 @ X20 @ X19 @ X18)
% 0.20/0.49          | ~ (l1_orders_2 @ X19)
% 0.20/0.49          | ~ (v5_orders_2 @ X19)
% 0.20/0.49          | ~ (v4_orders_2 @ X19)
% 0.20/0.49          | ~ (v3_orders_2 @ X19)
% 0.20/0.49          | (v2_struct_0 @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.49          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.49          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.20/0.49  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '25'])).
% 0.20/0.49  thf(d8_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.20/0.49         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((((sk_C) = (sk_D)))
% 0.20/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.49         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.20/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf(t69_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.49          | ((X21) = (k1_xboole_0))
% 0.20/0.49          | ~ (m1_orders_2 @ X23 @ X22 @ X21)
% 0.20/0.49          | ~ (m1_orders_2 @ X21 @ X22 @ X23)
% 0.20/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.49          | ~ (l1_orders_2 @ X22)
% 0.20/0.49          | ~ (v5_orders_2 @ X22)
% 0.20/0.49          | ~ (v4_orders_2 @ X22)
% 0.20/0.49          | ~ (v3_orders_2 @ X22)
% 0.20/0.49          | (v2_struct_0 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.20/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.49          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.20/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.49          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((sk_C) = (k1_xboole_0))
% 0.20/0.49        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.20/0.49        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.20/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.49  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '47'])).
% 0.20/0.49  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.20/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf('51', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t82_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.49         (~ (m1_orders_1 @ X24 @ (k1_orders_1 @ (u1_struct_0 @ X25)))
% 0.20/0.49          | ~ (m2_orders_2 @ X26 @ X25 @ X24)
% 0.20/0.49          | ~ (r1_xboole_0 @ X27 @ X26)
% 0.20/0.49          | ~ (m2_orders_2 @ X27 @ X25 @ X24)
% 0.20/0.49          | ~ (l1_orders_2 @ X25)
% 0.20/0.49          | ~ (v5_orders_2 @ X25)
% 0.20/0.49          | ~ (v4_orders_2 @ X25)
% 0.20/0.49          | ~ (v3_orders_2 @ X25)
% 0.20/0.49          | (v2_struct_0 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.49          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf('55', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.49          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | ~ (r1_xboole_0 @ sk_C @ X0)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['51', '59'])).
% 0.20/0.49  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ sk_C @ X0) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      ((~ (r1_xboole_0 @ sk_C @ k1_xboole_0))
% 0.20/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '62'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.49         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.49             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '47'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('66', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.49      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (![X6 : $i, X8 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.20/0.49      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.49  thf(t85_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X9 @ X10)
% 0.20/0.49          | (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('sup+', [status(thm)], ['68', '71'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '64', '72'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('75', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['3', '73', '74'])).
% 0.20/0.49  thf('76', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '75'])).
% 0.20/0.49  thf('77', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('78', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t83_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.49                   ( ( ( C ) != ( D ) ) =>
% 0.20/0.49                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.20/0.49                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.49         (~ (m1_orders_1 @ X28 @ (k1_orders_1 @ (u1_struct_0 @ X29)))
% 0.20/0.49          | ~ (m2_orders_2 @ X30 @ X29 @ X28)
% 0.20/0.49          | (m1_orders_2 @ X30 @ X29 @ X31)
% 0.20/0.49          | (m1_orders_2 @ X31 @ X29 @ X30)
% 0.20/0.49          | ((X31) = (X30))
% 0.20/0.49          | ~ (m2_orders_2 @ X31 @ X29 @ X28)
% 0.20/0.49          | ~ (l1_orders_2 @ X29)
% 0.20/0.49          | ~ (v5_orders_2 @ X29)
% 0.20/0.49          | ~ (v4_orders_2 @ X29)
% 0.20/0.49          | ~ (v3_orders_2 @ X29)
% 0.20/0.49          | (v2_struct_0 @ X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.49          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.49          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.49  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.49          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.49          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.20/0.49  thf('87', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.49          | (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.49          | (m1_orders_2 @ sk_D @ sk_A @ X0)
% 0.20/0.49          | ((sk_D) = (X0))
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['78', '86'])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((sk_D) = (sk_C))
% 0.20/0.49        | (m1_orders_2 @ sk_D @ sk_A @ sk_C)
% 0.20/0.49        | (m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['77', '87'])).
% 0.20/0.49  thf('89', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.49          | (r1_tarski @ X20 @ X18)
% 0.20/0.49          | ~ (m1_orders_2 @ X20 @ X19 @ X18)
% 0.20/0.49          | ~ (l1_orders_2 @ X19)
% 0.20/0.49          | ~ (v5_orders_2 @ X19)
% 0.20/0.49          | ~ (v4_orders_2 @ X19)
% 0.20/0.49          | ~ (v3_orders_2 @ X19)
% 0.20/0.49          | (v2_struct_0 @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.49          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.49  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('96', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.49          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.20/0.49  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('98', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['96', '97'])).
% 0.20/0.49  thf('99', plain,
% 0.20/0.49      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.20/0.49        | ((sk_D) = (sk_C))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (r1_tarski @ sk_D @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['88', '98'])).
% 0.20/0.49  thf('100', plain,
% 0.20/0.49      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.49         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('101', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['3', '73'])).
% 0.20/0.49  thf('102', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['100', '101'])).
% 0.20/0.49  thf('103', plain,
% 0.20/0.49      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_D) = (sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['99', '102'])).
% 0.20/0.49  thf('104', plain,
% 0.20/0.49      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('105', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.49  thf('106', plain,
% 0.20/0.49      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.49  thf('107', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i]:
% 0.20/0.49         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('108', plain,
% 0.20/0.49      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.20/0.49         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.49  thf('109', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['3', '73', '74'])).
% 0.20/0.49  thf('110', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['108', '109'])).
% 0.20/0.49  thf('111', plain, ((((sk_D) = (sk_C)) | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['103', '110'])).
% 0.20/0.49  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('113', plain, (((sk_D) = (sk_C))),
% 0.20/0.49      inference('clc', [status(thm)], ['111', '112'])).
% 0.20/0.49  thf('114', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['76', '113'])).
% 0.20/0.49  thf('115', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.49  thf('116', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['115'])).
% 0.20/0.49  thf('117', plain, ($false), inference('sup-', [status(thm)], ['114', '116'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
