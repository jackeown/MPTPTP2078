%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZwfD152ZLw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:13 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 872 expanded)
%              Number of leaves         :   37 ( 267 expanded)
%              Depth                    :   23
%              Number of atoms          : 1242 (13711 expanded)
%              Number of equality atoms :   38 ( 108 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    m2_orders_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( l1_orders_2 @ X42 )
      | ~ ( v5_orders_2 @ X42 )
      | ~ ( v4_orders_2 @ X42 )
      | ~ ( v3_orders_2 @ X42 )
      | ( v2_struct_0 @ X42 )
      | ~ ( m1_orders_1 @ X43 @ ( k1_orders_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m2_orders_2 @ X44 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
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
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( r1_tarski @ X47 @ X45 )
      | ~ ( m1_orders_2 @ X47 @ X46 @ X45 )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 )
      | ~ ( v4_orders_2 @ X46 )
      | ~ ( v3_orders_2 @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
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
    m2_orders_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X50 @ X49 @ X48 )
      | ~ ( m1_orders_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( l1_orders_2 @ X49 )
      | ~ ( v5_orders_2 @ X49 )
      | ~ ( v4_orders_2 @ X49 )
      | ~ ( v3_orders_2 @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X1 )
        = X0 )
      | ( r2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X1 @ X1 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('66',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('70',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','73'])).

thf('75',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('78',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_orders_1 @ X51 @ ( k1_orders_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( m2_orders_2 @ X53 @ X52 @ X51 )
      | ~ ( r1_xboole_0 @ X54 @ X53 )
      | ~ ( m2_orders_2 @ X54 @ X52 @ X51 )
      | ~ ( l1_orders_2 @ X52 )
      | ~ ( v5_orders_2 @ X52 )
      | ~ ( v4_orders_2 @ X52 )
      | ~ ( v3_orders_2 @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
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
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,(
    r2_xboole_0 @ k1_xboole_0 @ sk_D ),
    inference('sup-',[status(thm)],['74','88'])).

thf('90',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['50','89'])).

thf('91',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','90','91'])).

thf('93',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','92'])).

thf('94',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('97',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_orders_1 @ X55 @ ( k1_orders_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( m2_orders_2 @ X57 @ X56 @ X55 )
      | ( m1_orders_2 @ X57 @ X56 @ X58 )
      | ( m1_orders_2 @ X58 @ X56 @ X57 )
      | ( X58 = X57 )
      | ~ ( m2_orders_2 @ X58 @ X56 @ X55 )
      | ~ ( l1_orders_2 @ X56 )
      | ~ ( v5_orders_2 @ X56 )
      | ~ ( v4_orders_2 @ X56 )
      | ~ ( v3_orders_2 @ X56 )
      | ( v2_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['94','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('107',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( r1_tarski @ X47 @ X45 )
      | ~ ( m1_orders_2 @ X47 @ X46 @ X45 )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 )
      | ~ ( v4_orders_2 @ X46 )
      | ~ ( v3_orders_2 @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf('117',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('118',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','90'])).

thf('119',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('123',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('125',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','90','91'])).

thf('127',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['120','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['93','130'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('132',plain,(
    ! [X3: $i] :
      ~ ( r2_xboole_0 @ X3 @ X3 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('133',plain,(
    $false ),
    inference('sup-',[status(thm)],['131','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZwfD152ZLw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 1504 iterations in 0.662s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.90/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.10  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.10  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.90/1.10  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.90/1.10  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.90/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.10  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.10  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.90/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.10  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.90/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.90/1.10  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.90/1.10  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.90/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.10  thf(t84_orders_2, conjecture,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.90/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.90/1.10               ( ![D:$i]:
% 0.90/1.10                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.90/1.10                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i]:
% 0.90/1.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.90/1.10            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.90/1.10          ( ![B:$i]:
% 0.90/1.10            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10              ( ![C:$i]:
% 0.90/1.10                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.90/1.10                  ( ![D:$i]:
% 0.90/1.10                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.90/1.10                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.90/1.10  thf('0', plain,
% 0.90/1.10      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('2', plain,
% 0.90/1.10      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('3', plain,
% 0.90/1.10      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.90/1.10      inference('split', [status(esa)], ['2'])).
% 0.90/1.10  thf('4', plain,
% 0.90/1.10      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.90/1.10         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(dt_m2_orders_2, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.90/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.90/1.10         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.10       ( ![C:$i]:
% 0.90/1.10         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.90/1.10           ( ( v6_orders_2 @ C @ A ) & 
% 0.90/1.10             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.90/1.10         (~ (l1_orders_2 @ X42)
% 0.90/1.10          | ~ (v5_orders_2 @ X42)
% 0.90/1.10          | ~ (v4_orders_2 @ X42)
% 0.90/1.10          | ~ (v3_orders_2 @ X42)
% 0.90/1.10          | (v2_struct_0 @ X42)
% 0.90/1.10          | ~ (m1_orders_1 @ X43 @ (k1_orders_1 @ (u1_struct_0 @ X42)))
% 0.90/1.10          | (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.90/1.10          | ~ (m2_orders_2 @ X44 @ X42 @ X43))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10          | (v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (v3_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v4_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v5_orders_2 @ sk_A)
% 0.90/1.10          | ~ (l1_orders_2 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.10  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10          | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.90/1.10  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('15', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('clc', [status(thm)], ['13', '14'])).
% 0.90/1.10  thf('16', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['5', '15'])).
% 0.90/1.10  thf(t67_orders_2, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.90/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.90/1.10          | (r1_tarski @ X47 @ X45)
% 0.90/1.10          | ~ (m1_orders_2 @ X47 @ X46 @ X45)
% 0.90/1.10          | ~ (l1_orders_2 @ X46)
% 0.90/1.10          | ~ (v5_orders_2 @ X46)
% 0.90/1.10          | ~ (v4_orders_2 @ X46)
% 0.90/1.10          | ~ (v3_orders_2 @ X46)
% 0.90/1.10          | (v2_struct_0 @ X46))),
% 0.90/1.10      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.90/1.10  thf('18', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (v3_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v4_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v5_orders_2 @ sk_A)
% 0.90/1.10          | ~ (l1_orders_2 @ sk_A)
% 0.90/1.10          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.90/1.10          | (r1_tarski @ X0 @ sk_D))),
% 0.90/1.10      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.10  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('23', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.90/1.10          | (r1_tarski @ X0 @ sk_D))),
% 0.90/1.10      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.90/1.10  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('25', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.90/1.10      inference('clc', [status(thm)], ['23', '24'])).
% 0.90/1.10  thf('26', plain,
% 0.90/1.10      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['4', '25'])).
% 0.90/1.10  thf(d8_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.90/1.10       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.90/1.10  thf('27', plain,
% 0.90/1.10      (![X0 : $i, X2 : $i]:
% 0.90/1.10         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.10      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.90/1.10         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.10  thf('29', plain,
% 0.90/1.10      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['2'])).
% 0.90/1.10  thf('30', plain,
% 0.90/1.10      ((((sk_C) = (sk_D)))
% 0.90/1.10         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.90/1.10             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.90/1.10         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('32', plain,
% 0.90/1.10      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.90/1.10         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.90/1.10             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['30', '31'])).
% 0.90/1.10  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('34', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('clc', [status(thm)], ['13', '14'])).
% 0.90/1.10  thf('35', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.10  thf('36', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.10  thf(t69_orders_2, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.90/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.10                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf('37', plain,
% 0.90/1.10      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.90/1.10          | ((X48) = (k1_xboole_0))
% 0.90/1.10          | ~ (m1_orders_2 @ X50 @ X49 @ X48)
% 0.90/1.10          | ~ (m1_orders_2 @ X48 @ X49 @ X50)
% 0.90/1.10          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.90/1.10          | ~ (l1_orders_2 @ X49)
% 0.90/1.10          | ~ (v5_orders_2 @ X49)
% 0.90/1.10          | ~ (v4_orders_2 @ X49)
% 0.90/1.10          | ~ (v3_orders_2 @ X49)
% 0.90/1.10          | (v2_struct_0 @ X49))),
% 0.90/1.10      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.90/1.10  thf('38', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (v3_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v4_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v5_orders_2 @ sk_A)
% 0.90/1.10          | ~ (l1_orders_2 @ sk_A)
% 0.90/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.90/1.10          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.90/1.10          | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['36', '37'])).
% 0.90/1.10  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('43', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.90/1.10          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.90/1.10          | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.90/1.10  thf('44', plain,
% 0.90/1.10      ((((sk_C) = (k1_xboole_0))
% 0.90/1.10        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.90/1.10        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.90/1.10        | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['35', '43'])).
% 0.90/1.10  thf('45', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.90/1.10        | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.10      inference('simplify', [status(thm)], ['44'])).
% 0.90/1.10  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('47', plain,
% 0.90/1.10      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.90/1.10      inference('clc', [status(thm)], ['45', '46'])).
% 0.90/1.10  thf('48', plain,
% 0.90/1.10      ((((sk_C) = (k1_xboole_0)))
% 0.90/1.10         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.90/1.10             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['32', '47'])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['2'])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      ((~ (r2_xboole_0 @ k1_xboole_0 @ sk_D))
% 0.90/1.10         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.90/1.10             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.10  thf(t7_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.10  thf('51', plain,
% 0.90/1.10      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.90/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.10  thf(t43_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.90/1.10       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.90/1.10  thf('52', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.10         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.90/1.10          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.90/1.10  thf('53', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.90/1.10      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.10  thf(t4_subset_1, axiom,
% 0.90/1.10    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.90/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.10  thf(t3_subset, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.10  thf('55', plain,
% 0.90/1.10      (![X20 : $i, X21 : $i]:
% 0.90/1.10         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.10  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.10      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.10  thf(d10_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.10  thf('57', plain,
% 0.90/1.10      (![X4 : $i, X6 : $i]:
% 0.90/1.10         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('58', plain,
% 0.90/1.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['56', '57'])).
% 0.90/1.10  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['53', '58'])).
% 0.90/1.10  thf('60', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.90/1.10      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.10  thf('61', plain,
% 0.90/1.10      (![X0 : $i, X2 : $i]:
% 0.90/1.10         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.10      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.90/1.10  thf('62', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k4_xboole_0 @ X1 @ X1) = (X0))
% 0.90/1.10          | (r2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['60', '61'])).
% 0.90/1.10  thf('63', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((r2_xboole_0 @ k1_xboole_0 @ X0) | ((k4_xboole_0 @ X1 @ X1) = (X0)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['59', '62'])).
% 0.90/1.10  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['53', '58'])).
% 0.90/1.10  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.10      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.10  thf('66', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.10         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.90/1.10          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.90/1.10  thf('67', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ X0)),
% 0.90/1.10      inference('sup-', [status(thm)], ['65', '66'])).
% 0.90/1.10  thf('68', plain,
% 0.90/1.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['56', '57'])).
% 0.90/1.10  thf('69', plain,
% 0.90/1.10      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['67', '68'])).
% 0.90/1.10  thf(t83_xboole_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.10  thf('70', plain,
% 0.90/1.10      (![X12 : $i, X14 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.90/1.10  thf('71', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.10  thf('72', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.90/1.10      inference('simplify', [status(thm)], ['71'])).
% 0.90/1.10  thf('73', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.90/1.10      inference('sup+', [status(thm)], ['64', '72'])).
% 0.90/1.10  thf('74', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((r1_xboole_0 @ X0 @ X1) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['63', '73'])).
% 0.90/1.10  thf('75', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('76', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('77', plain,
% 0.90/1.10      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t82_orders_2, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.90/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.90/1.10               ( ![D:$i]:
% 0.90/1.10                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf('78', plain,
% 0.90/1.10      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.90/1.10         (~ (m1_orders_1 @ X51 @ (k1_orders_1 @ (u1_struct_0 @ X52)))
% 0.90/1.10          | ~ (m2_orders_2 @ X53 @ X52 @ X51)
% 0.90/1.10          | ~ (r1_xboole_0 @ X54 @ X53)
% 0.90/1.10          | ~ (m2_orders_2 @ X54 @ X52 @ X51)
% 0.90/1.10          | ~ (l1_orders_2 @ X52)
% 0.90/1.10          | ~ (v5_orders_2 @ X52)
% 0.90/1.10          | ~ (v4_orders_2 @ X52)
% 0.90/1.10          | ~ (v3_orders_2 @ X52)
% 0.90/1.10          | (v2_struct_0 @ X52))),
% 0.90/1.10      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.90/1.10  thf('79', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (v3_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v4_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v5_orders_2 @ sk_A)
% 0.90/1.10          | ~ (l1_orders_2 @ sk_A)
% 0.90/1.10          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.90/1.10          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.10  thf('80', plain, ((v3_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('81', plain, ((v4_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('82', plain, ((v5_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('84', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.90/1.10          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.90/1.10  thf('85', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | ~ (r1_xboole_0 @ sk_D @ X0)
% 0.90/1.10          | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['76', '84'])).
% 0.90/1.10  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('87', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (r1_xboole_0 @ sk_D @ X0) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('clc', [status(thm)], ['85', '86'])).
% 0.90/1.10  thf('88', plain, (~ (r1_xboole_0 @ sk_D @ sk_C)),
% 0.90/1.10      inference('sup-', [status(thm)], ['75', '87'])).
% 0.90/1.10  thf('89', plain, ((r2_xboole_0 @ k1_xboole_0 @ sk_D)),
% 0.90/1.10      inference('sup-', [status(thm)], ['74', '88'])).
% 0.90/1.10  thf('90', plain,
% 0.90/1.10      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.90/1.10      inference('demod', [status(thm)], ['50', '89'])).
% 0.90/1.10  thf('91', plain,
% 0.90/1.10      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('92', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)], ['3', '90', '91'])).
% 0.90/1.10  thf('93', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['1', '92'])).
% 0.90/1.10  thf('94', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('95', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('96', plain,
% 0.90/1.10      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t83_orders_2, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.90/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.90/1.10               ( ![D:$i]:
% 0.90/1.10                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.90/1.10                   ( ( ( C ) != ( D ) ) =>
% 0.90/1.10                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.90/1.10                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf('97', plain,
% 0.90/1.10      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.90/1.10         (~ (m1_orders_1 @ X55 @ (k1_orders_1 @ (u1_struct_0 @ X56)))
% 0.90/1.10          | ~ (m2_orders_2 @ X57 @ X56 @ X55)
% 0.90/1.10          | (m1_orders_2 @ X57 @ X56 @ X58)
% 0.90/1.10          | (m1_orders_2 @ X58 @ X56 @ X57)
% 0.90/1.10          | ((X58) = (X57))
% 0.90/1.10          | ~ (m2_orders_2 @ X58 @ X56 @ X55)
% 0.90/1.10          | ~ (l1_orders_2 @ X56)
% 0.90/1.10          | ~ (v5_orders_2 @ X56)
% 0.90/1.10          | ~ (v4_orders_2 @ X56)
% 0.90/1.10          | ~ (v3_orders_2 @ X56)
% 0.90/1.10          | (v2_struct_0 @ X56))),
% 0.90/1.10      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.90/1.10  thf('98', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (v3_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v4_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v5_orders_2 @ sk_A)
% 0.90/1.10          | ~ (l1_orders_2 @ sk_A)
% 0.90/1.10          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | ((X0) = (X1))
% 0.90/1.10          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.90/1.10          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.90/1.10          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['96', '97'])).
% 0.90/1.10  thf('99', plain, ((v3_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('100', plain, ((v4_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('101', plain, ((v5_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('103', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | ((X0) = (X1))
% 0.90/1.10          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.90/1.10          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.90/1.10          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.90/1.10  thf('104', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.90/1.10          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.90/1.10          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.90/1.10          | ((sk_C) = (X0))
% 0.90/1.10          | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['95', '103'])).
% 0.90/1.10  thf('105', plain,
% 0.90/1.10      (((v2_struct_0 @ sk_A)
% 0.90/1.10        | ((sk_C) = (sk_D))
% 0.90/1.10        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.90/1.10        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.90/1.10      inference('sup-', [status(thm)], ['94', '104'])).
% 0.90/1.10  thf('106', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.10  thf('107', plain,
% 0.90/1.10      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.90/1.10          | (r1_tarski @ X47 @ X45)
% 0.90/1.10          | ~ (m1_orders_2 @ X47 @ X46 @ X45)
% 0.90/1.10          | ~ (l1_orders_2 @ X46)
% 0.90/1.10          | ~ (v5_orders_2 @ X46)
% 0.90/1.10          | ~ (v4_orders_2 @ X46)
% 0.90/1.10          | ~ (v3_orders_2 @ X46)
% 0.90/1.10          | (v2_struct_0 @ X46))),
% 0.90/1.10      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.90/1.10  thf('108', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (v3_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v4_orders_2 @ sk_A)
% 0.90/1.10          | ~ (v5_orders_2 @ sk_A)
% 0.90/1.10          | ~ (l1_orders_2 @ sk_A)
% 0.90/1.10          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.90/1.10          | (r1_tarski @ X0 @ sk_C))),
% 0.90/1.10      inference('sup-', [status(thm)], ['106', '107'])).
% 0.90/1.10  thf('109', plain, ((v3_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('110', plain, ((v4_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('111', plain, ((v5_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('112', plain, ((l1_orders_2 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('113', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((v2_struct_0 @ sk_A)
% 0.90/1.10          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.90/1.10          | (r1_tarski @ X0 @ sk_C))),
% 0.90/1.10      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.90/1.10  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('115', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.90/1.10      inference('clc', [status(thm)], ['113', '114'])).
% 0.90/1.10  thf('116', plain,
% 0.90/1.10      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.90/1.10        | ((sk_C) = (sk_D))
% 0.90/1.10        | (v2_struct_0 @ sk_A)
% 0.90/1.10        | (r1_tarski @ sk_D @ sk_C))),
% 0.90/1.10      inference('sup-', [status(thm)], ['105', '115'])).
% 0.90/1.10  thf('117', plain,
% 0.90/1.10      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.90/1.10         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['2'])).
% 0.90/1.10  thf('118', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)], ['3', '90'])).
% 0.90/1.10  thf('119', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 0.90/1.10  thf('120', plain,
% 0.90/1.10      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['116', '119'])).
% 0.90/1.10  thf('121', plain,
% 0.90/1.10      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('122', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.90/1.10      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.90/1.10  thf('123', plain,
% 0.90/1.10      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['121', '122'])).
% 0.90/1.10  thf('124', plain,
% 0.90/1.10      (![X4 : $i, X6 : $i]:
% 0.90/1.10         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('125', plain,
% 0.90/1.10      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.90/1.10         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['123', '124'])).
% 0.90/1.10  thf('126', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)], ['3', '90', '91'])).
% 0.90/1.10  thf('127', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['125', '126'])).
% 0.90/1.10  thf('128', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.90/1.10      inference('clc', [status(thm)], ['120', '127'])).
% 0.90/1.10  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('130', plain, (((sk_C) = (sk_D))),
% 0.90/1.10      inference('clc', [status(thm)], ['128', '129'])).
% 0.90/1.10  thf('131', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.90/1.10      inference('demod', [status(thm)], ['93', '130'])).
% 0.90/1.10  thf(irreflexivity_r2_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.90/1.10  thf('132', plain, (![X3 : $i]: ~ (r2_xboole_0 @ X3 @ X3)),
% 0.90/1.10      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.90/1.10  thf('133', plain, ($false), inference('sup-', [status(thm)], ['131', '132'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
