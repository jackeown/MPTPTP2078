%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gzORoxXxnG

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:16 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 738 expanded)
%              Number of leaves         :   36 ( 222 expanded)
%              Depth                    :   23
%              Number of atoms          : 1177 (12745 expanded)
%              Number of equality atoms :   34 (  77 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m2_orders_2 @ X23 @ X21 @ X22 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X26 @ X24 )
      | ~ ( m1_orders_2 @ X26 @ X25 @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X29 @ X28 @ X27 )
      | ~ ( m1_orders_2 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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

thf('49',plain,
    ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
   <= ~ ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,
    ( ~ ( r2_xboole_0 @ k1_xboole_0 @ sk_D )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('51',plain,(
    ! [X15: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X15 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k4_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r2_xboole_0 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t58_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_xboole_0 @ X2 @ X0 )
      | ~ ( r2_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
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
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('64',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_orders_1 @ X30 @ ( k1_orders_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ ( u1_struct_0 @ X31 ) ) @ X32 )
      | ~ ( m2_orders_2 @ X32 @ X31 @ X30 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_D ),
    inference('sup-',[status(thm)],['62','72'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('75',plain,(
    ~ ( r1_tarski @ sk_D @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r2_xboole_0 @ k1_xboole_0 @ sk_D ),
    inference('sup-',[status(thm)],['61','75'])).

thf('77',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['50','76'])).

thf('78',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','77','78'])).

thf('80',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('81',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
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

thf('84',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_orders_1 @ X33 @ ( k1_orders_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m2_orders_2 @ X35 @ X34 @ X33 )
      | ( m1_orders_2 @ X35 @ X34 @ X36 )
      | ( m1_orders_2 @ X36 @ X34 @ X35 )
      | ( X36 = X35 )
      | ~ ( m2_orders_2 @ X36 @ X34 @ X33 )
      | ~ ( l1_orders_2 @ X34 )
      | ~ ( v5_orders_2 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v3_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('85',plain,(
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
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X26 @ X24 )
      | ~ ( m1_orders_2 @ X26 @ X25 @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['92','102'])).

thf('104',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('105',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','77'])).

thf('106',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('110',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','77','78'])).

thf('114',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['80','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('120',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    $false ),
    inference('sup-',[status(thm)],['118','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gzORoxXxnG
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.08  % Solved by: fo/fo7.sh
% 0.91/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.08  % done 1274 iterations in 0.636s
% 0.91/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.08  % SZS output start Refutation
% 0.91/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.08  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.91/1.08  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.91/1.08  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.91/1.08  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.91/1.08  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.91/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.08  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.91/1.08  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.91/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.08  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.91/1.08  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.91/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.08  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.91/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.08  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.91/1.08  thf(t84_orders_2, conjecture,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.08         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.08       ( ![B:$i]:
% 0.91/1.08         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.08           ( ![C:$i]:
% 0.91/1.08             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.91/1.08               ( ![D:$i]:
% 0.91/1.08                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.91/1.08                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.91/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.08    (~( ![A:$i]:
% 0.91/1.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.09            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.09          ( ![B:$i]:
% 0.91/1.09            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.09              ( ![C:$i]:
% 0.91/1.09                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.91/1.09                  ( ![D:$i]:
% 0.91/1.09                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.91/1.09                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.91/1.09    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.91/1.09  thf('0', plain,
% 0.91/1.09      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('1', plain,
% 0.91/1.09      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('2', plain,
% 0.91/1.09      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('3', plain,
% 0.91/1.09      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.91/1.09      inference('split', [status(esa)], ['2'])).
% 0.91/1.09  thf('4', plain,
% 0.91/1.09      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.91/1.09         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('6', plain,
% 0.91/1.09      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(dt_m2_orders_2, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.91/1.09         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.09       ( ![C:$i]:
% 0.91/1.09         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.91/1.09           ( ( v6_orders_2 @ C @ A ) & 
% 0.91/1.09             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.91/1.09  thf('7', plain,
% 0.91/1.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.09         (~ (l1_orders_2 @ X21)
% 0.91/1.09          | ~ (v5_orders_2 @ X21)
% 0.91/1.09          | ~ (v4_orders_2 @ X21)
% 0.91/1.09          | ~ (v3_orders_2 @ X21)
% 0.91/1.09          | (v2_struct_0 @ X21)
% 0.91/1.09          | ~ (m1_orders_1 @ X22 @ (k1_orders_1 @ (u1_struct_0 @ X21)))
% 0.91/1.09          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.91/1.09          | ~ (m2_orders_2 @ X23 @ X21 @ X22))),
% 0.91/1.09      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.91/1.09  thf('8', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.91/1.09          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.09          | (v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (v3_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v4_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v5_orders_2 @ sk_A)
% 0.91/1.09          | ~ (l1_orders_2 @ sk_A))),
% 0.91/1.09      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.09  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('13', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.91/1.09          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.09          | (v2_struct_0 @ sk_A))),
% 0.91/1.09      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.91/1.09  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('15', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.09          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.91/1.09      inference('clc', [status(thm)], ['13', '14'])).
% 0.91/1.09  thf('16', plain,
% 0.91/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['5', '15'])).
% 0.91/1.09  thf(t67_orders_2, axiom,
% 0.91/1.09    (![A:$i]:
% 0.91/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.09       ( ![B:$i]:
% 0.91/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.09           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.91/1.09  thf('17', plain,
% 0.91/1.09      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.09         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.09          | (r1_tarski @ X26 @ X24)
% 0.91/1.09          | ~ (m1_orders_2 @ X26 @ X25 @ X24)
% 0.91/1.09          | ~ (l1_orders_2 @ X25)
% 0.91/1.09          | ~ (v5_orders_2 @ X25)
% 0.91/1.09          | ~ (v4_orders_2 @ X25)
% 0.91/1.09          | ~ (v3_orders_2 @ X25)
% 0.91/1.09          | (v2_struct_0 @ X25))),
% 0.91/1.09      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.91/1.09  thf('18', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (v3_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v4_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v5_orders_2 @ sk_A)
% 0.91/1.09          | ~ (l1_orders_2 @ sk_A)
% 0.91/1.09          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.91/1.09          | (r1_tarski @ X0 @ sk_D))),
% 0.91/1.09      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.09  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('23', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.91/1.09          | (r1_tarski @ X0 @ sk_D))),
% 0.91/1.09      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.91/1.09  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('25', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.91/1.09      inference('clc', [status(thm)], ['23', '24'])).
% 0.91/1.09  thf('26', plain,
% 0.91/1.09      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['4', '25'])).
% 0.91/1.09  thf(d8_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.91/1.09       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.91/1.09  thf('27', plain,
% 0.91/1.09      (![X0 : $i, X2 : $i]:
% 0.91/1.09         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.09      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.91/1.09  thf('28', plain,
% 0.91/1.09      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.91/1.09         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.09  thf('29', plain,
% 0.91/1.09      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.91/1.09      inference('split', [status(esa)], ['2'])).
% 0.91/1.09  thf('30', plain,
% 0.91/1.09      ((((sk_C) = (sk_D)))
% 0.91/1.09         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.91/1.09             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.09  thf('31', plain,
% 0.91/1.09      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.91/1.09         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('32', plain,
% 0.91/1.09      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.91/1.09         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.91/1.09             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['30', '31'])).
% 0.91/1.09  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('34', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.09          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.91/1.09      inference('clc', [status(thm)], ['13', '14'])).
% 0.91/1.09  thf('35', plain,
% 0.91/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.09  thf('36', plain,
% 0.91/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.09  thf(t69_orders_2, axiom,
% 0.91/1.09    (![A:$i]:
% 0.91/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.09       ( ![B:$i]:
% 0.91/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.09           ( ![C:$i]:
% 0.91/1.09             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.09               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.91/1.09                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.91/1.09  thf('37', plain,
% 0.91/1.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.09         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.91/1.09          | ((X27) = (k1_xboole_0))
% 0.91/1.09          | ~ (m1_orders_2 @ X29 @ X28 @ X27)
% 0.91/1.09          | ~ (m1_orders_2 @ X27 @ X28 @ X29)
% 0.91/1.09          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.91/1.09          | ~ (l1_orders_2 @ X28)
% 0.91/1.09          | ~ (v5_orders_2 @ X28)
% 0.91/1.09          | ~ (v4_orders_2 @ X28)
% 0.91/1.09          | ~ (v3_orders_2 @ X28)
% 0.91/1.09          | (v2_struct_0 @ X28))),
% 0.91/1.09      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.91/1.09  thf('38', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (v3_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v4_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v5_orders_2 @ sk_A)
% 0.91/1.09          | ~ (l1_orders_2 @ sk_A)
% 0.91/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.09          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.91/1.09          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.91/1.09          | ((sk_C) = (k1_xboole_0)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['36', '37'])).
% 0.91/1.09  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('43', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.09          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.91/1.09          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.91/1.09          | ((sk_C) = (k1_xboole_0)))),
% 0.91/1.09      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.91/1.09  thf('44', plain,
% 0.91/1.09      ((((sk_C) = (k1_xboole_0))
% 0.91/1.09        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.91/1.09        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.91/1.09        | (v2_struct_0 @ sk_A))),
% 0.91/1.09      inference('sup-', [status(thm)], ['35', '43'])).
% 0.91/1.09  thf('45', plain,
% 0.91/1.09      (((v2_struct_0 @ sk_A)
% 0.91/1.09        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.91/1.09        | ((sk_C) = (k1_xboole_0)))),
% 0.91/1.09      inference('simplify', [status(thm)], ['44'])).
% 0.91/1.09  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('47', plain,
% 0.91/1.09      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.91/1.09      inference('clc', [status(thm)], ['45', '46'])).
% 0.91/1.09  thf('48', plain,
% 0.91/1.09      ((((sk_C) = (k1_xboole_0)))
% 0.91/1.09         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.91/1.09             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['32', '47'])).
% 0.91/1.09  thf('49', plain,
% 0.91/1.09      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.91/1.09      inference('split', [status(esa)], ['2'])).
% 0.91/1.09  thf('50', plain,
% 0.91/1.09      ((~ (r2_xboole_0 @ k1_xboole_0 @ sk_D))
% 0.91/1.09         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.91/1.09             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['48', '49'])).
% 0.91/1.09  thf(t61_xboole_1, axiom,
% 0.91/1.09    (![A:$i]:
% 0.91/1.09     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.91/1.09  thf('51', plain,
% 0.91/1.09      (![X15 : $i]:
% 0.91/1.09         ((r2_xboole_0 @ k1_xboole_0 @ X15) | ((X15) = (k1_xboole_0)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.91/1.09  thf(d10_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.09  thf('52', plain,
% 0.91/1.09      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.91/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.09  thf('53', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.91/1.09      inference('simplify', [status(thm)], ['52'])).
% 0.91/1.09  thf(t109_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.91/1.09  thf('54', plain,
% 0.91/1.09      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.91/1.09         (~ (r1_tarski @ X9 @ X10)
% 0.91/1.09          | (r1_tarski @ (k4_xboole_0 @ X9 @ X11) @ X10))),
% 0.91/1.09      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.91/1.09  thf('55', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.91/1.09      inference('sup-', [status(thm)], ['53', '54'])).
% 0.91/1.09  thf(t58_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.91/1.09       ( r2_xboole_0 @ A @ C ) ))).
% 0.91/1.09  thf('56', plain,
% 0.91/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.09         (~ (r2_xboole_0 @ X12 @ X13)
% 0.91/1.09          | ~ (r1_tarski @ X13 @ X14)
% 0.91/1.09          | (r2_xboole_0 @ X12 @ X14))),
% 0.91/1.09      inference('cnf', [status(esa)], [t58_xboole_1])).
% 0.91/1.09  thf('57', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         ((r2_xboole_0 @ X2 @ X0)
% 0.91/1.09          | ~ (r2_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['55', '56'])).
% 0.91/1.09  thf('58', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.91/1.09          | (r2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.91/1.09      inference('sup-', [status(thm)], ['51', '57'])).
% 0.91/1.09  thf(l32_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.09  thf('59', plain,
% 0.91/1.09      (![X6 : $i, X7 : $i]:
% 0.91/1.09         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.91/1.09      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.91/1.09  thf('60', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.09          | (r2_xboole_0 @ k1_xboole_0 @ X1)
% 0.91/1.09          | (r1_tarski @ X1 @ X0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.09  thf('61', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((r1_tarski @ X1 @ X0) | (r2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.91/1.09      inference('simplify', [status(thm)], ['60'])).
% 0.91/1.09  thf('62', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('63', plain,
% 0.91/1.09      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(t79_orders_2, axiom,
% 0.91/1.09    (![A:$i]:
% 0.91/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.09       ( ![B:$i]:
% 0.91/1.09         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.09           ( ![C:$i]:
% 0.91/1.09             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.91/1.09               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.91/1.09  thf('64', plain,
% 0.91/1.09      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.91/1.09         (~ (m1_orders_1 @ X30 @ (k1_orders_1 @ (u1_struct_0 @ X31)))
% 0.91/1.09          | (r2_hidden @ (k1_funct_1 @ X30 @ (u1_struct_0 @ X31)) @ X32)
% 0.91/1.09          | ~ (m2_orders_2 @ X32 @ X31 @ X30)
% 0.91/1.09          | ~ (l1_orders_2 @ X31)
% 0.91/1.09          | ~ (v5_orders_2 @ X31)
% 0.91/1.09          | ~ (v4_orders_2 @ X31)
% 0.91/1.09          | ~ (v3_orders_2 @ X31)
% 0.91/1.09          | (v2_struct_0 @ X31))),
% 0.91/1.09      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.91/1.09  thf('65', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (v3_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v4_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v5_orders_2 @ sk_A)
% 0.91/1.09          | ~ (l1_orders_2 @ sk_A)
% 0.91/1.09          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.91/1.09          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.91/1.09      inference('sup-', [status(thm)], ['63', '64'])).
% 0.91/1.09  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('67', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('70', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.91/1.09          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.91/1.09      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.91/1.09  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('72', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.91/1.09          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.91/1.09      inference('clc', [status(thm)], ['70', '71'])).
% 0.91/1.09  thf('73', plain,
% 0.91/1.09      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_D)),
% 0.91/1.09      inference('sup-', [status(thm)], ['62', '72'])).
% 0.91/1.09  thf(t7_ordinal1, axiom,
% 0.91/1.09    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.09  thf('74', plain,
% 0.91/1.09      (![X16 : $i, X17 : $i]:
% 0.91/1.09         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.91/1.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.91/1.09  thf('75', plain,
% 0.91/1.09      (~ (r1_tarski @ sk_D @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['73', '74'])).
% 0.91/1.09  thf('76', plain, ((r2_xboole_0 @ k1_xboole_0 @ sk_D)),
% 0.91/1.09      inference('sup-', [status(thm)], ['61', '75'])).
% 0.91/1.09  thf('77', plain,
% 0.91/1.09      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.91/1.09      inference('demod', [status(thm)], ['50', '76'])).
% 0.91/1.09  thf('78', plain,
% 0.91/1.09      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('79', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.91/1.09      inference('sat_resolution*', [status(thm)], ['3', '77', '78'])).
% 0.91/1.09  thf('80', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.91/1.09      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 0.91/1.09  thf('81', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('82', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('83', plain,
% 0.91/1.09      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf(t83_orders_2, axiom,
% 0.91/1.09    (![A:$i]:
% 0.91/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.09         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.09       ( ![B:$i]:
% 0.91/1.09         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.09           ( ![C:$i]:
% 0.91/1.09             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.91/1.09               ( ![D:$i]:
% 0.91/1.09                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.91/1.09                   ( ( ( C ) != ( D ) ) =>
% 0.91/1.09                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.91/1.09                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.09  thf('84', plain,
% 0.91/1.09      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.91/1.09         (~ (m1_orders_1 @ X33 @ (k1_orders_1 @ (u1_struct_0 @ X34)))
% 0.91/1.09          | ~ (m2_orders_2 @ X35 @ X34 @ X33)
% 0.91/1.09          | (m1_orders_2 @ X35 @ X34 @ X36)
% 0.91/1.09          | (m1_orders_2 @ X36 @ X34 @ X35)
% 0.91/1.09          | ((X36) = (X35))
% 0.91/1.09          | ~ (m2_orders_2 @ X36 @ X34 @ X33)
% 0.91/1.09          | ~ (l1_orders_2 @ X34)
% 0.91/1.09          | ~ (v5_orders_2 @ X34)
% 0.91/1.09          | ~ (v4_orders_2 @ X34)
% 0.91/1.09          | ~ (v3_orders_2 @ X34)
% 0.91/1.09          | (v2_struct_0 @ X34))),
% 0.91/1.09      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.91/1.09  thf('85', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (v3_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v4_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v5_orders_2 @ sk_A)
% 0.91/1.09          | ~ (l1_orders_2 @ sk_A)
% 0.91/1.09          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.91/1.09          | ((X0) = (X1))
% 0.91/1.09          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.91/1.09          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.91/1.09          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.91/1.09      inference('sup-', [status(thm)], ['83', '84'])).
% 0.91/1.09  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('90', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.91/1.09          | ((X0) = (X1))
% 0.91/1.09          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.91/1.09          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.91/1.09          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.91/1.09      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.91/1.09  thf('91', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.91/1.09          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.91/1.09          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.91/1.09          | ((sk_C) = (X0))
% 0.91/1.09          | (v2_struct_0 @ sk_A))),
% 0.91/1.09      inference('sup-', [status(thm)], ['82', '90'])).
% 0.91/1.09  thf('92', plain,
% 0.91/1.09      (((v2_struct_0 @ sk_A)
% 0.91/1.09        | ((sk_C) = (sk_D))
% 0.91/1.09        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.91/1.09        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.91/1.09      inference('sup-', [status(thm)], ['81', '91'])).
% 0.91/1.09  thf('93', plain,
% 0.91/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.09  thf('94', plain,
% 0.91/1.09      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.09         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.09          | (r1_tarski @ X26 @ X24)
% 0.91/1.09          | ~ (m1_orders_2 @ X26 @ X25 @ X24)
% 0.91/1.09          | ~ (l1_orders_2 @ X25)
% 0.91/1.09          | ~ (v5_orders_2 @ X25)
% 0.91/1.09          | ~ (v4_orders_2 @ X25)
% 0.91/1.09          | ~ (v3_orders_2 @ X25)
% 0.91/1.09          | (v2_struct_0 @ X25))),
% 0.91/1.09      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.91/1.09  thf('95', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (v3_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v4_orders_2 @ sk_A)
% 0.91/1.09          | ~ (v5_orders_2 @ sk_A)
% 0.91/1.09          | ~ (l1_orders_2 @ sk_A)
% 0.91/1.09          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.91/1.09          | (r1_tarski @ X0 @ sk_C))),
% 0.91/1.09      inference('sup-', [status(thm)], ['93', '94'])).
% 0.91/1.09  thf('96', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('98', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('100', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((v2_struct_0 @ sk_A)
% 0.91/1.09          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.91/1.09          | (r1_tarski @ X0 @ sk_C))),
% 0.91/1.09      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.91/1.09  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('102', plain,
% 0.91/1.09      (![X0 : $i]:
% 0.91/1.09         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.91/1.09      inference('clc', [status(thm)], ['100', '101'])).
% 0.91/1.09  thf('103', plain,
% 0.91/1.09      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.91/1.09        | ((sk_C) = (sk_D))
% 0.91/1.09        | (v2_struct_0 @ sk_A)
% 0.91/1.09        | (r1_tarski @ sk_D @ sk_C))),
% 0.91/1.09      inference('sup-', [status(thm)], ['92', '102'])).
% 0.91/1.09  thf('104', plain,
% 0.91/1.09      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.91/1.09         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.91/1.09      inference('split', [status(esa)], ['2'])).
% 0.91/1.09  thf('105', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.91/1.09      inference('sat_resolution*', [status(thm)], ['3', '77'])).
% 0.91/1.09  thf('106', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.91/1.09      inference('simpl_trail', [status(thm)], ['104', '105'])).
% 0.91/1.09  thf('107', plain,
% 0.91/1.09      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['103', '106'])).
% 0.91/1.09  thf('108', plain,
% 0.91/1.09      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('109', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.91/1.09  thf('110', plain,
% 0.91/1.09      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['108', '109'])).
% 0.91/1.09  thf('111', plain,
% 0.91/1.09      (![X3 : $i, X5 : $i]:
% 0.91/1.09         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.91/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.09  thf('112', plain,
% 0.91/1.09      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.91/1.09         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['110', '111'])).
% 0.91/1.09  thf('113', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.91/1.09      inference('sat_resolution*', [status(thm)], ['3', '77', '78'])).
% 0.91/1.09  thf('114', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.91/1.09      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 0.91/1.09  thf('115', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.91/1.09      inference('clc', [status(thm)], ['107', '114'])).
% 0.91/1.09  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('117', plain, (((sk_C) = (sk_D))),
% 0.91/1.09      inference('clc', [status(thm)], ['115', '116'])).
% 0.91/1.09  thf('118', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.91/1.09      inference('demod', [status(thm)], ['80', '117'])).
% 0.91/1.09  thf('119', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.91/1.09  thf('120', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.91/1.09      inference('simplify', [status(thm)], ['119'])).
% 0.91/1.09  thf('121', plain, ($false), inference('sup-', [status(thm)], ['118', '120'])).
% 0.91/1.09  
% 0.91/1.09  % SZS output end Refutation
% 0.91/1.09  
% 0.91/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
