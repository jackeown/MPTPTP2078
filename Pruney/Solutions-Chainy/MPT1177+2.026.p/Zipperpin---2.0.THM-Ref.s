%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Z03XnMVDq

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 (1142 expanded)
%              Number of leaves         :   33 ( 335 expanded)
%              Depth                    :   26
%              Number of atoms          : 1148 (20818 expanded)
%              Number of equality atoms :   31 ( 104 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_orders_1 @ X18 @ ( k1_orders_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m2_orders_2 @ X19 @ X17 @ X18 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ X22 @ X20 )
      | ~ ( m1_orders_2 @ X22 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_orders_2 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_orders_1 @ X26 @ ( k1_orders_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m2_orders_2 @ X28 @ X27 @ X26 )
      | ~ ( r1_xboole_0 @ X29 @ X28 )
      | ~ ( m2_orders_2 @ X29 @ X27 @ X26 )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['61'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ! [X0: $i] :
        ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['50','71'])).

thf('73',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','72','73'])).

thf('75',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','74'])).

thf('76',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_orders_1 @ X30 @ ( k1_orders_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m2_orders_2 @ X32 @ X31 @ X30 )
      | ( m1_orders_2 @ X32 @ X31 @ X33 )
      | ( m1_orders_2 @ X33 @ X31 @ X32 )
      | ( X33 = X32 )
      | ~ ( m2_orders_2 @ X33 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('80',plain,(
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
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('89',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ X22 @ X20 )
      | ~ ( m1_orders_2 @ X22 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['87','97'])).

thf('99',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('100',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','72'])).

thf('101',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('105',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','72','73'])).

thf('109',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['102','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['75','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('115',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    $false ),
    inference('sup-',[status(thm)],['113','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6Z03XnMVDq
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:27 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 343 iterations in 0.104s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.56  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(t84_orders_2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.56                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.56                  ( ![D:$i]:
% 0.21/0.56                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.56                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.21/0.56         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_m2_orders_2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.56         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.56           ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.56             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l1_orders_2 @ X17)
% 0.21/0.56          | ~ (v5_orders_2 @ X17)
% 0.21/0.56          | ~ (v4_orders_2 @ X17)
% 0.21/0.56          | ~ (v3_orders_2 @ X17)
% 0.21/0.56          | (v2_struct_0 @ X17)
% 0.21/0.56          | ~ (m1_orders_1 @ X18 @ (k1_orders_1 @ (u1_struct_0 @ X17)))
% 0.21/0.56          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.56          | ~ (m2_orders_2 @ X19 @ X17 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.21/0.56  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.56      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '15'])).
% 0.21/0.56  thf(t67_orders_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56          | (r1_tarski @ X22 @ X20)
% 0.21/0.56          | ~ (m1_orders_2 @ X22 @ X21 @ X20)
% 0.21/0.56          | ~ (l1_orders_2 @ X21)
% 0.21/0.56          | ~ (v5_orders_2 @ X21)
% 0.21/0.56          | ~ (v4_orders_2 @ X21)
% 0.21/0.56          | ~ (v3_orders_2 @ X21)
% 0.21/0.56          | (v2_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.21/0.56          | (r1_tarski @ X0 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.21/0.56          | (r1_tarski @ X0 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.21/0.56  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.21/0.56      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '25'])).
% 0.21/0.56  thf(d8_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.56       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X2 : $i]:
% 0.21/0.56         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.21/0.56         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((((sk_C) = (sk_D)))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.21/0.56         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.56      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf(t69_orders_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.56          | ((X23) = (k1_xboole_0))
% 0.21/0.56          | ~ (m1_orders_2 @ X25 @ X24 @ X23)
% 0.21/0.56          | ~ (m1_orders_2 @ X23 @ X24 @ X25)
% 0.21/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.56          | ~ (l1_orders_2 @ X24)
% 0.21/0.56          | ~ (v5_orders_2 @ X24)
% 0.21/0.56          | ~ (v4_orders_2 @ X24)
% 0.21/0.56          | ~ (v3_orders_2 @ X24)
% 0.21/0.56          | (v2_struct_0 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.56          | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.56          | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((((sk_C) = (k1_xboole_0))
% 0.21/0.56        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.21/0.56        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.21/0.56        | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['35', '43'])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.21/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.56  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.21/0.56      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['32', '47'])).
% 0.21/0.56  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t82_orders_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         (~ (m1_orders_1 @ X26 @ (k1_orders_1 @ (u1_struct_0 @ X27)))
% 0.21/0.56          | ~ (m2_orders_2 @ X28 @ X27 @ X26)
% 0.21/0.56          | ~ (r1_xboole_0 @ X29 @ X28)
% 0.21/0.56          | ~ (m2_orders_2 @ X29 @ X27 @ X26)
% 0.21/0.56          | ~ (l1_orders_2 @ X27)
% 0.21/0.56          | ~ (v5_orders_2 @ X27)
% 0.21/0.56          | ~ (v4_orders_2 @ X27)
% 0.21/0.56          | ~ (v3_orders_2 @ X27)
% 0.21/0.56          | (v2_struct_0 @ X27))),
% 0.21/0.56      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.56          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.56  thf('55', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('56', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.56          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56           | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.56           | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['51', '59'])).
% 0.21/0.56  thf(d10_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('62', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.21/0.56      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.56  thf(l32_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X6 : $i, X8 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.56  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.56  thf(t36_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.21/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.56  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.56      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.56  thf(t106_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.56       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X9 @ X11)
% 0.21/0.56          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.21/0.56  thf('68', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      ((![X0 : $i]: (~ (m2_orders_2 @ X0 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('demod', [status(thm)], ['60', '68'])).
% 0.21/0.56  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      ((![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))
% 0.21/0.56         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.21/0.56             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['50', '71'])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('74', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['3', '72', '73'])).
% 0.21/0.56  thf('75', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['1', '74'])).
% 0.21/0.56  thf('76', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('77', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t83_orders_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.56                   ( ( ( C ) != ( D ) ) =>
% 0.21/0.56                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.21/0.56                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.56         (~ (m1_orders_1 @ X30 @ (k1_orders_1 @ (u1_struct_0 @ X31)))
% 0.21/0.56          | ~ (m2_orders_2 @ X32 @ X31 @ X30)
% 0.21/0.56          | (m1_orders_2 @ X32 @ X31 @ X33)
% 0.21/0.56          | (m1_orders_2 @ X33 @ X31 @ X32)
% 0.21/0.56          | ((X33) = (X32))
% 0.21/0.56          | ~ (m2_orders_2 @ X33 @ X31 @ X30)
% 0.21/0.56          | ~ (l1_orders_2 @ X31)
% 0.21/0.56          | ~ (v5_orders_2 @ X31)
% 0.21/0.56          | ~ (v4_orders_2 @ X31)
% 0.21/0.56          | ~ (v3_orders_2 @ X31)
% 0.21/0.56          | (v2_struct_0 @ X31))),
% 0.21/0.56      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56          | ((X0) = (X1))
% 0.21/0.56          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.56          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.56          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.56  thf('81', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('82', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('83', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56          | ((X0) = (X1))
% 0.21/0.56          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.56          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.56          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.56          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.56          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.21/0.56          | ((sk_C) = (X0))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['77', '85'])).
% 0.21/0.56  thf('87', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_A)
% 0.21/0.56        | ((sk_C) = (sk_D))
% 0.21/0.56        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.21/0.56        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['76', '86'])).
% 0.21/0.56  thf('88', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('89', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56          | (r1_tarski @ X22 @ X20)
% 0.21/0.56          | ~ (m1_orders_2 @ X22 @ X21 @ X20)
% 0.21/0.56          | ~ (l1_orders_2 @ X21)
% 0.21/0.56          | ~ (v5_orders_2 @ X21)
% 0.21/0.56          | ~ (v4_orders_2 @ X21)
% 0.21/0.56          | ~ (v3_orders_2 @ X21)
% 0.21/0.56          | (v2_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.56  thf('90', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.56          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.56  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('92', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('94', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('95', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.21/0.56          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 0.21/0.56  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.21/0.56      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.56  thf('98', plain,
% 0.21/0.56      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.21/0.56        | ((sk_C) = (sk_D))
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (r1_tarski @ sk_D @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['87', '97'])).
% 0.21/0.56  thf('99', plain,
% 0.21/0.56      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.21/0.56         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('100', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['3', '72'])).
% 0.21/0.56  thf('101', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['99', '100'])).
% 0.21/0.56  thf('102', plain,
% 0.21/0.56      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['98', '101'])).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('104', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.56  thf('106', plain,
% 0.21/0.56      (![X3 : $i, X5 : $i]:
% 0.21/0.56         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('107', plain,
% 0.21/0.56      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.21/0.56         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.56  thf('108', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['3', '72', '73'])).
% 0.21/0.56  thf('109', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['107', '108'])).
% 0.21/0.56  thf('110', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['102', '109'])).
% 0.21/0.56  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('112', plain, (((sk_C) = (sk_D))),
% 0.21/0.56      inference('clc', [status(thm)], ['110', '111'])).
% 0.21/0.56  thf('113', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['75', '112'])).
% 0.21/0.56  thf('114', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.56  thf('115', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.21/0.56      inference('simplify', [status(thm)], ['114'])).
% 0.21/0.56  thf('116', plain, ($false), inference('sup-', [status(thm)], ['113', '115'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
