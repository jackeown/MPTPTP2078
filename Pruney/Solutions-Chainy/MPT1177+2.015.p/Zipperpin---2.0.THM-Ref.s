%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pXgv1h891q

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:14 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  170 (1277 expanded)
%              Number of leaves         :   40 ( 384 expanded)
%              Depth                    :   23
%              Number of atoms          : 1229 (21730 expanded)
%              Number of equality atoms :   40 ( 156 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( l1_orders_2 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v3_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_orders_1 @ X40 @ ( k1_orders_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m2_orders_2 @ X41 @ X39 @ X40 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( r1_tarski @ X44 @ X42 )
      | ~ ( m1_orders_2 @ X44 @ X43 @ X42 )
      | ~ ( l1_orders_2 @ X43 )
      | ~ ( v5_orders_2 @ X43 )
      | ~ ( v4_orders_2 @ X43 )
      | ~ ( v3_orders_2 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X47 @ X46 @ X45 )
      | ~ ( m1_orders_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_orders_2 @ X46 )
      | ~ ( v5_orders_2 @ X46 )
      | ~ ( v4_orders_2 @ X46 )
      | ~ ( v3_orders_2 @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
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
    m2_orders_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_orders_1 @ X48 @ ( k1_orders_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( m2_orders_2 @ X50 @ X49 @ X48 )
      | ~ ( r1_xboole_0 @ X51 @ X50 )
      | ~ ( m2_orders_2 @ X51 @ X49 @ X48 )
      | ~ ( l1_orders_2 @ X49 )
      | ~ ( v5_orders_2 @ X49 )
      | ~ ( v4_orders_2 @ X49 )
      | ~ ( v3_orders_2 @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
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
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('68',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('82',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ( ( k4_xboole_0 @ X17 @ X19 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','84'])).

thf('86',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','85','86'])).

thf('88',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','87'])).

thf('89',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
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

thf('92',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_orders_1 @ X52 @ ( k1_orders_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( m2_orders_2 @ X54 @ X53 @ X52 )
      | ( m1_orders_2 @ X54 @ X53 @ X55 )
      | ( m1_orders_2 @ X55 @ X53 @ X54 )
      | ( X55 = X54 )
      | ~ ( m2_orders_2 @ X55 @ X53 @ X52 )
      | ~ ( l1_orders_2 @ X53 )
      | ~ ( v5_orders_2 @ X53 )
      | ~ ( v4_orders_2 @ X53 )
      | ~ ( v3_orders_2 @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('93',plain,(
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
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['89','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('102',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( r1_tarski @ X44 @ X42 )
      | ~ ( m1_orders_2 @ X44 @ X43 @ X42 )
      | ~ ( l1_orders_2 @ X43 )
      | ~ ( v5_orders_2 @ X43 )
      | ~ ( v4_orders_2 @ X43 )
      | ~ ( v3_orders_2 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['100','110'])).

thf('112',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('113',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','85'])).

thf('114',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('118',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','85','86'])).

thf('122',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['115','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['88','125'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('127',plain,(
    ! [X3: $i] :
      ~ ( r2_xboole_0 @ X3 @ X3 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('128',plain,(
    $false ),
    inference('sup-',[status(thm)],['126','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pXgv1h891q
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.67/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.90  % Solved by: fo/fo7.sh
% 0.67/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.90  % done 764 iterations in 0.438s
% 0.67/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.90  % SZS output start Refutation
% 0.67/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.90  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.90  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.67/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.90  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.67/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.67/0.90  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.67/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.90  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.67/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.90  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.67/0.90  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.67/0.90  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.67/0.90  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.67/0.90  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.67/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.90  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.67/0.90  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.67/0.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.67/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.90  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.67/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(t84_orders_2, conjecture,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.67/0.90       ( ![B:$i]:
% 0.67/0.90         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.90           ( ![C:$i]:
% 0.67/0.90             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.67/0.90               ( ![D:$i]:
% 0.67/0.90                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.67/0.90                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.67/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.90    (~( ![A:$i]:
% 0.67/0.90        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.90            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.67/0.90          ( ![B:$i]:
% 0.67/0.90            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.90              ( ![C:$i]:
% 0.67/0.90                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.67/0.90                  ( ![D:$i]:
% 0.67/0.90                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.67/0.90                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.67/0.90    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.67/0.90  thf('0', plain,
% 0.67/0.90      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('1', plain,
% 0.67/0.90      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('2', plain,
% 0.67/0.90      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('3', plain,
% 0.67/0.90      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.90      inference('split', [status(esa)], ['2'])).
% 0.67/0.90  thf('4', plain,
% 0.67/0.90      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.67/0.90         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('6', plain,
% 0.67/0.90      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(dt_m2_orders_2, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.67/0.90         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.90       ( ![C:$i]:
% 0.67/0.90         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.67/0.90           ( ( v6_orders_2 @ C @ A ) & 
% 0.67/0.90             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.67/0.90  thf('7', plain,
% 0.67/0.90      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.67/0.90         (~ (l1_orders_2 @ X39)
% 0.67/0.90          | ~ (v5_orders_2 @ X39)
% 0.67/0.90          | ~ (v4_orders_2 @ X39)
% 0.67/0.90          | ~ (v3_orders_2 @ X39)
% 0.67/0.90          | (v2_struct_0 @ X39)
% 0.67/0.90          | ~ (m1_orders_1 @ X40 @ (k1_orders_1 @ (u1_struct_0 @ X39)))
% 0.67/0.90          | (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.67/0.90          | ~ (m2_orders_2 @ X41 @ X39 @ X40))),
% 0.67/0.90      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.67/0.90  thf('8', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.90          | (v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.67/0.90          | ~ (l1_orders_2 @ sk_A))),
% 0.67/0.90      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.90  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('13', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.90          | (v2_struct_0 @ sk_A))),
% 0.67/0.90      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.67/0.90  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('15', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.90          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.67/0.90      inference('clc', [status(thm)], ['13', '14'])).
% 0.67/0.90  thf('16', plain,
% 0.67/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['5', '15'])).
% 0.67/0.90  thf(t67_orders_2, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.67/0.90       ( ![B:$i]:
% 0.67/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.90           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.67/0.90  thf('17', plain,
% 0.67/0.90      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.67/0.90         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.67/0.90          | (r1_tarski @ X44 @ X42)
% 0.67/0.90          | ~ (m1_orders_2 @ X44 @ X43 @ X42)
% 0.67/0.90          | ~ (l1_orders_2 @ X43)
% 0.67/0.90          | ~ (v5_orders_2 @ X43)
% 0.67/0.90          | ~ (v4_orders_2 @ X43)
% 0.67/0.90          | ~ (v3_orders_2 @ X43)
% 0.67/0.90          | (v2_struct_0 @ X43))),
% 0.67/0.90      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.67/0.90  thf('18', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.67/0.90          | ~ (l1_orders_2 @ sk_A)
% 0.67/0.90          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.67/0.90          | (r1_tarski @ X0 @ sk_D))),
% 0.67/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.67/0.90  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('23', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.67/0.90          | (r1_tarski @ X0 @ sk_D))),
% 0.67/0.90      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.67/0.90  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('25', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.67/0.90      inference('clc', [status(thm)], ['23', '24'])).
% 0.67/0.90  thf('26', plain,
% 0.67/0.90      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['4', '25'])).
% 0.67/0.90  thf(d8_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.67/0.90       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.67/0.90  thf('27', plain,
% 0.67/0.90      (![X0 : $i, X2 : $i]:
% 0.67/0.90         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.90      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.67/0.90  thf('28', plain,
% 0.67/0.90      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.67/0.90         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['26', '27'])).
% 0.67/0.90  thf('29', plain,
% 0.67/0.90      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.67/0.90      inference('split', [status(esa)], ['2'])).
% 0.67/0.90  thf('30', plain,
% 0.67/0.90      ((((sk_C) = (sk_D)))
% 0.67/0.90         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.67/0.90             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.90  thf('31', plain,
% 0.67/0.90      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.67/0.90         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('32', plain,
% 0.67/0.90      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.67/0.90         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.67/0.90             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['30', '31'])).
% 0.67/0.90  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('34', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.90          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.67/0.90      inference('clc', [status(thm)], ['13', '14'])).
% 0.67/0.90  thf('35', plain,
% 0.67/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.90  thf('36', plain,
% 0.67/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.90  thf(t69_orders_2, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.67/0.90       ( ![B:$i]:
% 0.67/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.90           ( ![C:$i]:
% 0.67/0.90             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.90               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.67/0.90                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.67/0.90  thf('37', plain,
% 0.67/0.90      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.67/0.90         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.67/0.90          | ((X45) = (k1_xboole_0))
% 0.67/0.90          | ~ (m1_orders_2 @ X47 @ X46 @ X45)
% 0.67/0.90          | ~ (m1_orders_2 @ X45 @ X46 @ X47)
% 0.67/0.90          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.67/0.90          | ~ (l1_orders_2 @ X46)
% 0.67/0.90          | ~ (v5_orders_2 @ X46)
% 0.67/0.90          | ~ (v4_orders_2 @ X46)
% 0.67/0.90          | ~ (v3_orders_2 @ X46)
% 0.67/0.90          | (v2_struct_0 @ X46))),
% 0.67/0.90      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.67/0.90  thf('38', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.67/0.90          | ~ (l1_orders_2 @ sk_A)
% 0.67/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.90          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.67/0.90          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.67/0.90          | ((sk_C) = (k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['36', '37'])).
% 0.67/0.90  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('43', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.90          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.67/0.90          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.67/0.90          | ((sk_C) = (k1_xboole_0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.67/0.90  thf('44', plain,
% 0.67/0.90      ((((sk_C) = (k1_xboole_0))
% 0.67/0.90        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.67/0.90        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.67/0.90        | (v2_struct_0 @ sk_A))),
% 0.67/0.90      inference('sup-', [status(thm)], ['35', '43'])).
% 0.67/0.90  thf('45', plain,
% 0.67/0.90      (((v2_struct_0 @ sk_A)
% 0.67/0.90        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.67/0.90        | ((sk_C) = (k1_xboole_0)))),
% 0.67/0.90      inference('simplify', [status(thm)], ['44'])).
% 0.67/0.90  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('47', plain,
% 0.67/0.90      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.67/0.90      inference('clc', [status(thm)], ['45', '46'])).
% 0.67/0.90  thf('48', plain,
% 0.67/0.90      ((((sk_C) = (k1_xboole_0)))
% 0.67/0.90         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.67/0.90             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['32', '47'])).
% 0.67/0.90  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('50', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('51', plain,
% 0.67/0.90      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(t82_orders_2, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.67/0.90       ( ![B:$i]:
% 0.67/0.90         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.90           ( ![C:$i]:
% 0.67/0.90             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.67/0.90               ( ![D:$i]:
% 0.67/0.90                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.67/0.90  thf('52', plain,
% 0.67/0.90      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.67/0.90         (~ (m1_orders_1 @ X48 @ (k1_orders_1 @ (u1_struct_0 @ X49)))
% 0.67/0.90          | ~ (m2_orders_2 @ X50 @ X49 @ X48)
% 0.67/0.90          | ~ (r1_xboole_0 @ X51 @ X50)
% 0.67/0.90          | ~ (m2_orders_2 @ X51 @ X49 @ X48)
% 0.67/0.90          | ~ (l1_orders_2 @ X49)
% 0.67/0.90          | ~ (v5_orders_2 @ X49)
% 0.67/0.90          | ~ (v4_orders_2 @ X49)
% 0.67/0.90          | ~ (v3_orders_2 @ X49)
% 0.67/0.90          | (v2_struct_0 @ X49))),
% 0.67/0.90      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.67/0.90  thf('53', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.67/0.90          | ~ (l1_orders_2 @ sk_A)
% 0.67/0.90          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.67/0.90          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['51', '52'])).
% 0.67/0.90  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('55', plain, ((v4_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('56', plain, ((v5_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('58', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.67/0.90          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.67/0.90      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.67/0.90  thf('59', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | ~ (r1_xboole_0 @ sk_C @ X0)
% 0.67/0.90          | (v2_struct_0 @ sk_A))),
% 0.67/0.90      inference('sup-', [status(thm)], ['50', '58'])).
% 0.67/0.90  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('61', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (r1_xboole_0 @ sk_C @ X0) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.67/0.90      inference('clc', [status(thm)], ['59', '60'])).
% 0.67/0.90  thf('62', plain, (~ (r1_xboole_0 @ sk_C @ sk_C)),
% 0.67/0.90      inference('sup-', [status(thm)], ['49', '61'])).
% 0.67/0.90  thf('63', plain,
% 0.67/0.90      ((~ (r1_xboole_0 @ sk_C @ k1_xboole_0))
% 0.67/0.90         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.67/0.90             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['48', '62'])).
% 0.67/0.90  thf('64', plain,
% 0.67/0.90      ((((sk_C) = (k1_xboole_0)))
% 0.67/0.90         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.67/0.90             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['32', '47'])).
% 0.67/0.90  thf(t7_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.90  thf('65', plain,
% 0.67/0.90      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.67/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.67/0.90  thf(t43_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.67/0.90       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.67/0.90  thf('66', plain,
% 0.67/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.67/0.90         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.67/0.90          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.67/0.90  thf('67', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.67/0.90      inference('sup-', [status(thm)], ['65', '66'])).
% 0.67/0.90  thf(t29_mcart_1, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.67/0.90          ( ![B:$i]:
% 0.67/0.90            ( ~( ( r2_hidden @ B @ A ) & 
% 0.67/0.90                 ( ![C:$i,D:$i,E:$i]:
% 0.67/0.90                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.67/0.90                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.90  thf('68', plain,
% 0.67/0.90      (![X32 : $i]:
% 0.67/0.90         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.67/0.90      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.67/0.90  thf(t7_ordinal1, axiom,
% 0.67/0.90    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.90  thf('69', plain,
% 0.67/0.90      (![X30 : $i, X31 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 0.67/0.90      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.67/0.90  thf('70', plain,
% 0.67/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['68', '69'])).
% 0.67/0.90  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['67', '70'])).
% 0.67/0.90  thf('72', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.67/0.90      inference('sup-', [status(thm)], ['65', '66'])).
% 0.67/0.90  thf('73', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.67/0.90      inference('sup+', [status(thm)], ['71', '72'])).
% 0.67/0.90  thf('74', plain,
% 0.67/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.67/0.90         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.67/0.90          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.67/0.90  thf('75', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ X0)),
% 0.67/0.90      inference('sup-', [status(thm)], ['73', '74'])).
% 0.67/0.90  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['67', '70'])).
% 0.67/0.90  thf('77', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.67/0.90      inference('sup+', [status(thm)], ['71', '72'])).
% 0.67/0.90  thf(d10_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.90  thf('78', plain,
% 0.67/0.90      (![X6 : $i, X8 : $i]:
% 0.67/0.90         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.67/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.90  thf('79', plain,
% 0.67/0.90      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['77', '78'])).
% 0.67/0.90  thf('80', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['76', '79'])).
% 0.67/0.90  thf('81', plain,
% 0.67/0.90      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['75', '80'])).
% 0.67/0.90  thf(t83_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.90  thf('82', plain,
% 0.67/0.90      (![X17 : $i, X19 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X17 @ X19) | ((k4_xboole_0 @ X17 @ X19) != (X17)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.90  thf('83', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['81', '82'])).
% 0.67/0.90  thf('84', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.67/0.90      inference('simplify', [status(thm)], ['83'])).
% 0.67/0.90  thf('85', plain,
% 0.67/0.90      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.67/0.90      inference('demod', [status(thm)], ['63', '64', '84'])).
% 0.67/0.90  thf('86', plain,
% 0.67/0.90      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('87', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.90      inference('sat_resolution*', [status(thm)], ['3', '85', '86'])).
% 0.67/0.90  thf('88', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.67/0.90      inference('simpl_trail', [status(thm)], ['1', '87'])).
% 0.67/0.90  thf('89', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('90', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('91', plain,
% 0.67/0.90      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(t83_orders_2, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.67/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.67/0.90       ( ![B:$i]:
% 0.67/0.90         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.90           ( ![C:$i]:
% 0.67/0.90             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.67/0.90               ( ![D:$i]:
% 0.67/0.90                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.67/0.90                   ( ( ( C ) != ( D ) ) =>
% 0.67/0.90                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.67/0.90                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.90  thf('92', plain,
% 0.67/0.90      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.67/0.90         (~ (m1_orders_1 @ X52 @ (k1_orders_1 @ (u1_struct_0 @ X53)))
% 0.67/0.90          | ~ (m2_orders_2 @ X54 @ X53 @ X52)
% 0.67/0.90          | (m1_orders_2 @ X54 @ X53 @ X55)
% 0.67/0.90          | (m1_orders_2 @ X55 @ X53 @ X54)
% 0.67/0.90          | ((X55) = (X54))
% 0.67/0.90          | ~ (m2_orders_2 @ X55 @ X53 @ X52)
% 0.67/0.90          | ~ (l1_orders_2 @ X53)
% 0.67/0.90          | ~ (v5_orders_2 @ X53)
% 0.67/0.90          | ~ (v4_orders_2 @ X53)
% 0.67/0.90          | ~ (v3_orders_2 @ X53)
% 0.67/0.90          | (v2_struct_0 @ X53))),
% 0.67/0.90      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.67/0.90  thf('93', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.67/0.90          | ~ (l1_orders_2 @ sk_A)
% 0.67/0.90          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | ((X0) = (X1))
% 0.67/0.90          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.67/0.90          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.67/0.90          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['91', '92'])).
% 0.67/0.90  thf('94', plain, ((v3_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('95', plain, ((v4_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('97', plain, ((l1_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('98', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | ((X0) = (X1))
% 0.67/0.90          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.67/0.90          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.67/0.90          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.67/0.90      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.67/0.90  thf('99', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.67/0.90          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.67/0.90          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.67/0.90          | ((sk_C) = (X0))
% 0.67/0.90          | (v2_struct_0 @ sk_A))),
% 0.67/0.90      inference('sup-', [status(thm)], ['90', '98'])).
% 0.67/0.90  thf('100', plain,
% 0.67/0.90      (((v2_struct_0 @ sk_A)
% 0.67/0.90        | ((sk_C) = (sk_D))
% 0.67/0.90        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.67/0.90        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.67/0.90      inference('sup-', [status(thm)], ['89', '99'])).
% 0.67/0.90  thf('101', plain,
% 0.67/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.90  thf('102', plain,
% 0.67/0.90      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.67/0.90         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.67/0.90          | (r1_tarski @ X44 @ X42)
% 0.67/0.90          | ~ (m1_orders_2 @ X44 @ X43 @ X42)
% 0.67/0.90          | ~ (l1_orders_2 @ X43)
% 0.67/0.90          | ~ (v5_orders_2 @ X43)
% 0.67/0.90          | ~ (v4_orders_2 @ X43)
% 0.67/0.90          | ~ (v3_orders_2 @ X43)
% 0.67/0.90          | (v2_struct_0 @ X43))),
% 0.67/0.90      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.67/0.90  thf('103', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.67/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.67/0.90          | ~ (l1_orders_2 @ sk_A)
% 0.67/0.90          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.67/0.90          | (r1_tarski @ X0 @ sk_C))),
% 0.67/0.90      inference('sup-', [status(thm)], ['101', '102'])).
% 0.67/0.90  thf('104', plain, ((v3_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('105', plain, ((v4_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('106', plain, ((v5_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('108', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((v2_struct_0 @ sk_A)
% 0.67/0.90          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.67/0.90          | (r1_tarski @ X0 @ sk_C))),
% 0.67/0.90      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.67/0.90  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('110', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.67/0.90      inference('clc', [status(thm)], ['108', '109'])).
% 0.67/0.90  thf('111', plain,
% 0.67/0.90      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.67/0.90        | ((sk_C) = (sk_D))
% 0.67/0.90        | (v2_struct_0 @ sk_A)
% 0.67/0.90        | (r1_tarski @ sk_D @ sk_C))),
% 0.67/0.90      inference('sup-', [status(thm)], ['100', '110'])).
% 0.67/0.90  thf('112', plain,
% 0.67/0.90      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.67/0.90         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.67/0.90      inference('split', [status(esa)], ['2'])).
% 0.67/0.90  thf('113', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.67/0.90      inference('sat_resolution*', [status(thm)], ['3', '85'])).
% 0.67/0.90  thf('114', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.67/0.90      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 0.67/0.90  thf('115', plain,
% 0.67/0.90      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['111', '114'])).
% 0.67/0.90  thf('116', plain,
% 0.67/0.90      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('117', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.67/0.90  thf('118', plain,
% 0.67/0.90      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['116', '117'])).
% 0.67/0.90  thf('119', plain,
% 0.67/0.90      (![X6 : $i, X8 : $i]:
% 0.67/0.90         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.67/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.90  thf('120', plain,
% 0.67/0.90      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.67/0.90         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['118', '119'])).
% 0.67/0.90  thf('121', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.67/0.90      inference('sat_resolution*', [status(thm)], ['3', '85', '86'])).
% 0.67/0.90  thf('122', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.67/0.90      inference('simpl_trail', [status(thm)], ['120', '121'])).
% 0.67/0.90  thf('123', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.67/0.90      inference('clc', [status(thm)], ['115', '122'])).
% 0.67/0.90  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('125', plain, (((sk_C) = (sk_D))),
% 0.67/0.90      inference('clc', [status(thm)], ['123', '124'])).
% 0.67/0.90  thf('126', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.67/0.90      inference('demod', [status(thm)], ['88', '125'])).
% 0.67/0.90  thf(irreflexivity_r2_xboole_0, axiom,
% 0.67/0.90    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.67/0.90  thf('127', plain, (![X3 : $i]: ~ (r2_xboole_0 @ X3 @ X3)),
% 0.67/0.90      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.67/0.90  thf('128', plain, ($false), inference('sup-', [status(thm)], ['126', '127'])).
% 0.67/0.90  
% 0.67/0.90  % SZS output end Refutation
% 0.67/0.90  
% 0.67/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
