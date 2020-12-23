%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.751EgYRnGE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:14 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  168 (1241 expanded)
%              Number of leaves         :   40 ( 372 expanded)
%              Depth                    :   23
%              Number of atoms          : 1217 (21460 expanded)
%              Number of equality atoms :   38 ( 138 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( l1_orders_2 @ X50 )
      | ~ ( v5_orders_2 @ X50 )
      | ~ ( v4_orders_2 @ X50 )
      | ~ ( v3_orders_2 @ X50 )
      | ( v2_struct_0 @ X50 )
      | ~ ( m1_orders_1 @ X51 @ ( k1_orders_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( m2_orders_2 @ X52 @ X50 @ X51 ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( r1_tarski @ X55 @ X53 )
      | ~ ( m1_orders_2 @ X55 @ X54 @ X53 )
      | ~ ( l1_orders_2 @ X54 )
      | ~ ( v5_orders_2 @ X54 )
      | ~ ( v4_orders_2 @ X54 )
      | ~ ( v3_orders_2 @ X54 )
      | ( v2_struct_0 @ X54 ) ) ),
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
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( X56 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X58 @ X57 @ X56 )
      | ~ ( m1_orders_2 @ X56 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( l1_orders_2 @ X57 )
      | ~ ( v5_orders_2 @ X57 )
      | ~ ( v4_orders_2 @ X57 )
      | ~ ( v3_orders_2 @ X57 )
      | ( v2_struct_0 @ X57 ) ) ),
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
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_orders_1 @ X59 @ ( k1_orders_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( m2_orders_2 @ X61 @ X60 @ X59 )
      | ~ ( r1_xboole_0 @ X62 @ X61 )
      | ~ ( m2_orders_2 @ X62 @ X60 @ X59 )
      | ~ ( l1_orders_2 @ X60 )
      | ~ ( v5_orders_2 @ X60 )
      | ~ ( v4_orders_2 @ X60 )
      | ~ ( v3_orders_2 @ X60 )
      | ( v2_struct_0 @ X60 ) ) ),
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

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('68',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X41 @ X40 ) ) ),
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
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('80',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ( ( k4_xboole_0 @ X17 @ X19 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','82'])).

thf('84',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','83','84'])).

thf('86',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','85'])).

thf('87',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
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

thf('90',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_orders_1 @ X63 @ ( k1_orders_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( m2_orders_2 @ X65 @ X64 @ X63 )
      | ( m1_orders_2 @ X65 @ X64 @ X66 )
      | ( m1_orders_2 @ X66 @ X64 @ X65 )
      | ( X66 = X65 )
      | ~ ( m2_orders_2 @ X66 @ X64 @ X63 )
      | ~ ( l1_orders_2 @ X64 )
      | ~ ( v5_orders_2 @ X64 )
      | ~ ( v4_orders_2 @ X64 )
      | ~ ( v3_orders_2 @ X64 )
      | ( v2_struct_0 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('91',plain,(
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
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['87','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('100',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( r1_tarski @ X55 @ X53 )
      | ~ ( m1_orders_2 @ X55 @ X54 @ X53 )
      | ~ ( l1_orders_2 @ X54 )
      | ~ ( v5_orders_2 @ X54 )
      | ~ ( v4_orders_2 @ X54 )
      | ~ ( v3_orders_2 @ X54 )
      | ( v2_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['98','108'])).

thf('110',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('111',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','83'])).

thf('112',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('116',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','83','84'])).

thf('120',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['113','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['86','123'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('125',plain,(
    ! [X3: $i] :
      ~ ( r2_xboole_0 @ X3 @ X3 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('126',plain,(
    $false ),
    inference('sup-',[status(thm)],['124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.751EgYRnGE
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.30/1.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.30/1.51  % Solved by: fo/fo7.sh
% 1.30/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.51  % done 2308 iterations in 1.058s
% 1.30/1.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.30/1.51  % SZS output start Refutation
% 1.30/1.51  thf(sk_C_type, type, sk_C: $i).
% 1.30/1.51  thf(sk_D_type, type, sk_D: $i).
% 1.30/1.51  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 1.30/1.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.30/1.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.30/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.30/1.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.30/1.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.30/1.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.30/1.51  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 1.30/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.30/1.51  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 1.30/1.51  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.30/1.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.30/1.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 1.30/1.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.30/1.51  thf(sk_B_type, type, sk_B: $i > $i).
% 1.30/1.51  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 1.30/1.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.30/1.51  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 1.30/1.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.30/1.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.30/1.51  thf(t84_orders_2, conjecture,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.30/1.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.30/1.51       ( ![B:$i]:
% 1.30/1.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.30/1.51           ( ![C:$i]:
% 1.30/1.51             ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.30/1.51               ( ![D:$i]:
% 1.30/1.51                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 1.30/1.51                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 1.30/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.51    (~( ![A:$i]:
% 1.30/1.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.30/1.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.30/1.51          ( ![B:$i]:
% 1.30/1.51            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.30/1.51              ( ![C:$i]:
% 1.30/1.51                ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.30/1.51                  ( ![D:$i]:
% 1.30/1.51                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 1.30/1.51                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 1.30/1.51    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 1.30/1.51  thf('0', plain,
% 1.30/1.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('1', plain,
% 1.30/1.51      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 1.30/1.51      inference('split', [status(esa)], ['0'])).
% 1.30/1.51  thf('2', plain,
% 1.30/1.51      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('3', plain,
% 1.30/1.52      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 1.30/1.52      inference('split', [status(esa)], ['2'])).
% 1.30/1.52  thf('4', plain,
% 1.30/1.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 1.30/1.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('split', [status(esa)], ['0'])).
% 1.30/1.52  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('6', plain,
% 1.30/1.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf(dt_m2_orders_2, axiom,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.30/1.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.30/1.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.30/1.52       ( ![C:$i]:
% 1.30/1.52         ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.30/1.52           ( ( v6_orders_2 @ C @ A ) & 
% 1.30/1.52             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.30/1.52  thf('7', plain,
% 1.30/1.52      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.30/1.52         (~ (l1_orders_2 @ X50)
% 1.30/1.52          | ~ (v5_orders_2 @ X50)
% 1.30/1.52          | ~ (v4_orders_2 @ X50)
% 1.30/1.52          | ~ (v3_orders_2 @ X50)
% 1.30/1.52          | (v2_struct_0 @ X50)
% 1.30/1.52          | ~ (m1_orders_1 @ X51 @ (k1_orders_1 @ (u1_struct_0 @ X50)))
% 1.30/1.52          | (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 1.30/1.52          | ~ (m2_orders_2 @ X52 @ X50 @ X51))),
% 1.30/1.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 1.30/1.52  thf('8', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.30/1.52          | (v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (v3_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v4_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v5_orders_2 @ sk_A)
% 1.30/1.52          | ~ (l1_orders_2 @ sk_A))),
% 1.30/1.52      inference('sup-', [status(thm)], ['6', '7'])).
% 1.30/1.52  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('13', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.30/1.52          | (v2_struct_0 @ sk_A))),
% 1.30/1.52      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 1.30/1.52  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('15', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.30/1.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 1.30/1.52      inference('clc', [status(thm)], ['13', '14'])).
% 1.30/1.52  thf('16', plain,
% 1.30/1.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['5', '15'])).
% 1.30/1.52  thf(t67_orders_2, axiom,
% 1.30/1.52    (![A:$i]:
% 1.30/1.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.30/1.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.30/1.52       ( ![B:$i]:
% 1.30/1.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.30/1.52           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 1.30/1.52  thf('17', plain,
% 1.30/1.52      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.30/1.52         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.30/1.52          | (r1_tarski @ X55 @ X53)
% 1.30/1.52          | ~ (m1_orders_2 @ X55 @ X54 @ X53)
% 1.30/1.52          | ~ (l1_orders_2 @ X54)
% 1.30/1.52          | ~ (v5_orders_2 @ X54)
% 1.30/1.52          | ~ (v4_orders_2 @ X54)
% 1.30/1.52          | ~ (v3_orders_2 @ X54)
% 1.30/1.52          | (v2_struct_0 @ X54))),
% 1.30/1.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 1.30/1.52  thf('18', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (v3_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v4_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v5_orders_2 @ sk_A)
% 1.30/1.52          | ~ (l1_orders_2 @ sk_A)
% 1.30/1.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 1.30/1.52          | (r1_tarski @ X0 @ sk_D))),
% 1.30/1.52      inference('sup-', [status(thm)], ['16', '17'])).
% 1.30/1.52  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('23', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 1.30/1.52          | (r1_tarski @ X0 @ sk_D))),
% 1.30/1.52      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 1.30/1.52  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('25', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 1.30/1.52      inference('clc', [status(thm)], ['23', '24'])).
% 1.30/1.52  thf('26', plain,
% 1.30/1.52      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['4', '25'])).
% 1.30/1.52  thf(d8_xboole_0, axiom,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( r2_xboole_0 @ A @ B ) <=>
% 1.30/1.52       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 1.30/1.52  thf('27', plain,
% 1.30/1.52      (![X0 : $i, X2 : $i]:
% 1.30/1.52         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 1.30/1.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.30/1.52  thf('28', plain,
% 1.30/1.52      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 1.30/1.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['26', '27'])).
% 1.30/1.52  thf('29', plain,
% 1.30/1.52      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 1.30/1.52      inference('split', [status(esa)], ['2'])).
% 1.30/1.52  thf('30', plain,
% 1.30/1.52      ((((sk_C) = (sk_D)))
% 1.30/1.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 1.30/1.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['28', '29'])).
% 1.30/1.52  thf('31', plain,
% 1.30/1.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 1.30/1.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('split', [status(esa)], ['0'])).
% 1.30/1.52  thf('32', plain,
% 1.30/1.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 1.30/1.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 1.30/1.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.30/1.52  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('34', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.30/1.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 1.30/1.52      inference('clc', [status(thm)], ['13', '14'])).
% 1.30/1.52  thf('35', plain,
% 1.30/1.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.52  thf('36', plain,
% 1.30/1.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.52  thf(t69_orders_2, axiom,
% 1.30/1.52    (![A:$i]:
% 1.30/1.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.30/1.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.30/1.52       ( ![B:$i]:
% 1.30/1.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.30/1.52           ( ![C:$i]:
% 1.30/1.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.30/1.52               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.30/1.52                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 1.30/1.52  thf('37', plain,
% 1.30/1.52      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.30/1.52         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 1.30/1.52          | ((X56) = (k1_xboole_0))
% 1.30/1.52          | ~ (m1_orders_2 @ X58 @ X57 @ X56)
% 1.30/1.52          | ~ (m1_orders_2 @ X56 @ X57 @ X58)
% 1.30/1.52          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 1.30/1.52          | ~ (l1_orders_2 @ X57)
% 1.30/1.52          | ~ (v5_orders_2 @ X57)
% 1.30/1.52          | ~ (v4_orders_2 @ X57)
% 1.30/1.52          | ~ (v3_orders_2 @ X57)
% 1.30/1.52          | (v2_struct_0 @ X57))),
% 1.30/1.52      inference('cnf', [status(esa)], [t69_orders_2])).
% 1.30/1.52  thf('38', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (v3_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v4_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v5_orders_2 @ sk_A)
% 1.30/1.52          | ~ (l1_orders_2 @ sk_A)
% 1.30/1.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.30/1.52          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 1.30/1.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 1.30/1.52          | ((sk_C) = (k1_xboole_0)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['36', '37'])).
% 1.30/1.52  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('43', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.30/1.52          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 1.30/1.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 1.30/1.52          | ((sk_C) = (k1_xboole_0)))),
% 1.30/1.52      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 1.30/1.52  thf('44', plain,
% 1.30/1.52      ((((sk_C) = (k1_xboole_0))
% 1.30/1.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 1.30/1.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 1.30/1.52        | (v2_struct_0 @ sk_A))),
% 1.30/1.52      inference('sup-', [status(thm)], ['35', '43'])).
% 1.30/1.52  thf('45', plain,
% 1.30/1.52      (((v2_struct_0 @ sk_A)
% 1.30/1.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 1.30/1.52        | ((sk_C) = (k1_xboole_0)))),
% 1.30/1.52      inference('simplify', [status(thm)], ['44'])).
% 1.30/1.52  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('47', plain,
% 1.30/1.52      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 1.30/1.52      inference('clc', [status(thm)], ['45', '46'])).
% 1.30/1.52  thf('48', plain,
% 1.30/1.52      ((((sk_C) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 1.30/1.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['32', '47'])).
% 1.30/1.52  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('50', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('51', plain,
% 1.30/1.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf(t82_orders_2, axiom,
% 1.30/1.52    (![A:$i]:
% 1.30/1.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.30/1.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.30/1.52       ( ![B:$i]:
% 1.30/1.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.30/1.52           ( ![C:$i]:
% 1.30/1.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.30/1.52               ( ![D:$i]:
% 1.30/1.52                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.30/1.52  thf('52', plain,
% 1.30/1.52      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 1.30/1.52         (~ (m1_orders_1 @ X59 @ (k1_orders_1 @ (u1_struct_0 @ X60)))
% 1.30/1.52          | ~ (m2_orders_2 @ X61 @ X60 @ X59)
% 1.30/1.52          | ~ (r1_xboole_0 @ X62 @ X61)
% 1.30/1.52          | ~ (m2_orders_2 @ X62 @ X60 @ X59)
% 1.30/1.52          | ~ (l1_orders_2 @ X60)
% 1.30/1.52          | ~ (v5_orders_2 @ X60)
% 1.30/1.52          | ~ (v4_orders_2 @ X60)
% 1.30/1.52          | ~ (v3_orders_2 @ X60)
% 1.30/1.52          | (v2_struct_0 @ X60))),
% 1.30/1.52      inference('cnf', [status(esa)], [t82_orders_2])).
% 1.30/1.52  thf('53', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (v3_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v4_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v5_orders_2 @ sk_A)
% 1.30/1.52          | ~ (l1_orders_2 @ sk_A)
% 1.30/1.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.30/1.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 1.30/1.52      inference('sup-', [status(thm)], ['51', '52'])).
% 1.30/1.52  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('55', plain, ((v4_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('56', plain, ((v5_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('58', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.30/1.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 1.30/1.52      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 1.30/1.52  thf('59', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | ~ (r1_xboole_0 @ sk_C @ X0)
% 1.30/1.52          | (v2_struct_0 @ sk_A))),
% 1.30/1.52      inference('sup-', [status(thm)], ['50', '58'])).
% 1.30/1.52  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('61', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (r1_xboole_0 @ sk_C @ X0) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 1.30/1.52      inference('clc', [status(thm)], ['59', '60'])).
% 1.30/1.52  thf('62', plain, (~ (r1_xboole_0 @ sk_C @ sk_C)),
% 1.30/1.52      inference('sup-', [status(thm)], ['49', '61'])).
% 1.30/1.52  thf('63', plain,
% 1.30/1.52      ((~ (r1_xboole_0 @ sk_C @ k1_xboole_0))
% 1.30/1.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 1.30/1.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['48', '62'])).
% 1.30/1.52  thf('64', plain,
% 1.30/1.52      ((((sk_C) = (k1_xboole_0)))
% 1.30/1.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 1.30/1.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['32', '47'])).
% 1.30/1.52  thf(t7_xboole_1, axiom,
% 1.30/1.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.30/1.52  thf('65', plain,
% 1.30/1.52      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 1.30/1.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.30/1.52  thf(t43_xboole_1, axiom,
% 1.30/1.52    (![A:$i,B:$i,C:$i]:
% 1.30/1.52     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.30/1.52       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.30/1.52  thf('66', plain,
% 1.30/1.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.30/1.52         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.30/1.52          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.30/1.52      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.30/1.52  thf('67', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.30/1.52      inference('sup-', [status(thm)], ['65', '66'])).
% 1.30/1.52  thf(t34_mcart_1, axiom,
% 1.30/1.52    (![A:$i]:
% 1.30/1.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.30/1.52          ( ![B:$i]:
% 1.30/1.52            ( ~( ( r2_hidden @ B @ A ) & 
% 1.30/1.52                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 1.30/1.52                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.30/1.52                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 1.30/1.52  thf('68', plain,
% 1.30/1.52      (![X42 : $i]:
% 1.30/1.52         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 1.30/1.52      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.30/1.52  thf(t7_ordinal1, axiom,
% 1.30/1.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.30/1.52  thf('69', plain,
% 1.30/1.52      (![X40 : $i, X41 : $i]:
% 1.30/1.52         (~ (r2_hidden @ X40 @ X41) | ~ (r1_tarski @ X41 @ X40))),
% 1.30/1.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.30/1.52  thf('70', plain,
% 1.30/1.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.52  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.30/1.52      inference('sup-', [status(thm)], ['67', '70'])).
% 1.30/1.52  thf('72', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.30/1.52      inference('sup-', [status(thm)], ['65', '66'])).
% 1.30/1.52  thf('73', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.30/1.52      inference('sup+', [status(thm)], ['71', '72'])).
% 1.30/1.52  thf('74', plain,
% 1.30/1.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.30/1.52         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.30/1.52          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.30/1.52      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.30/1.52  thf('75', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ X0)),
% 1.30/1.52      inference('sup-', [status(thm)], ['73', '74'])).
% 1.30/1.52  thf('76', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.30/1.52      inference('sup+', [status(thm)], ['71', '72'])).
% 1.30/1.52  thf(d10_xboole_0, axiom,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.30/1.52  thf('77', plain,
% 1.30/1.52      (![X6 : $i, X8 : $i]:
% 1.30/1.52         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.30/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.52  thf('78', plain,
% 1.30/1.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['76', '77'])).
% 1.30/1.52  thf('79', plain,
% 1.30/1.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.30/1.52      inference('sup-', [status(thm)], ['75', '78'])).
% 1.30/1.52  thf(t83_xboole_1, axiom,
% 1.30/1.52    (![A:$i,B:$i]:
% 1.30/1.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.30/1.52  thf('80', plain,
% 1.30/1.52      (![X17 : $i, X19 : $i]:
% 1.30/1.52         ((r1_xboole_0 @ X17 @ X19) | ((k4_xboole_0 @ X17 @ X19) != (X17)))),
% 1.30/1.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.30/1.52  thf('81', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.30/1.52      inference('sup-', [status(thm)], ['79', '80'])).
% 1.30/1.52  thf('82', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.30/1.52      inference('simplify', [status(thm)], ['81'])).
% 1.30/1.52  thf('83', plain,
% 1.30/1.52      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 1.30/1.52      inference('demod', [status(thm)], ['63', '64', '82'])).
% 1.30/1.52  thf('84', plain,
% 1.30/1.52      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 1.30/1.52      inference('split', [status(esa)], ['0'])).
% 1.30/1.52  thf('85', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 1.30/1.52      inference('sat_resolution*', [status(thm)], ['3', '83', '84'])).
% 1.30/1.52  thf('86', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 1.30/1.52      inference('simpl_trail', [status(thm)], ['1', '85'])).
% 1.30/1.52  thf('87', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('88', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('89', plain,
% 1.30/1.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf(t83_orders_2, axiom,
% 1.30/1.52    (![A:$i]:
% 1.30/1.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.30/1.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.30/1.52       ( ![B:$i]:
% 1.30/1.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.30/1.52           ( ![C:$i]:
% 1.30/1.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.30/1.52               ( ![D:$i]:
% 1.30/1.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 1.30/1.52                   ( ( ( C ) != ( D ) ) =>
% 1.30/1.52                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 1.30/1.52                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.30/1.52  thf('90', plain,
% 1.30/1.52      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 1.30/1.52         (~ (m1_orders_1 @ X63 @ (k1_orders_1 @ (u1_struct_0 @ X64)))
% 1.30/1.52          | ~ (m2_orders_2 @ X65 @ X64 @ X63)
% 1.30/1.52          | (m1_orders_2 @ X65 @ X64 @ X66)
% 1.30/1.52          | (m1_orders_2 @ X66 @ X64 @ X65)
% 1.30/1.52          | ((X66) = (X65))
% 1.30/1.52          | ~ (m2_orders_2 @ X66 @ X64 @ X63)
% 1.30/1.52          | ~ (l1_orders_2 @ X64)
% 1.30/1.52          | ~ (v5_orders_2 @ X64)
% 1.30/1.52          | ~ (v4_orders_2 @ X64)
% 1.30/1.52          | ~ (v3_orders_2 @ X64)
% 1.30/1.52          | (v2_struct_0 @ X64))),
% 1.30/1.52      inference('cnf', [status(esa)], [t83_orders_2])).
% 1.30/1.52  thf('91', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (v3_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v4_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v5_orders_2 @ sk_A)
% 1.30/1.52          | ~ (l1_orders_2 @ sk_A)
% 1.30/1.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | ((X0) = (X1))
% 1.30/1.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 1.30/1.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 1.30/1.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 1.30/1.52      inference('sup-', [status(thm)], ['89', '90'])).
% 1.30/1.52  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('96', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | ((X0) = (X1))
% 1.30/1.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 1.30/1.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 1.30/1.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 1.30/1.52      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 1.30/1.52  thf('97', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 1.30/1.52          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 1.30/1.52          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 1.30/1.52          | ((sk_C) = (X0))
% 1.30/1.52          | (v2_struct_0 @ sk_A))),
% 1.30/1.52      inference('sup-', [status(thm)], ['88', '96'])).
% 1.30/1.52  thf('98', plain,
% 1.30/1.52      (((v2_struct_0 @ sk_A)
% 1.30/1.52        | ((sk_C) = (sk_D))
% 1.30/1.52        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 1.30/1.52        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 1.30/1.52      inference('sup-', [status(thm)], ['87', '97'])).
% 1.30/1.52  thf('99', plain,
% 1.30/1.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.52  thf('100', plain,
% 1.30/1.52      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.30/1.52         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.30/1.52          | (r1_tarski @ X55 @ X53)
% 1.30/1.52          | ~ (m1_orders_2 @ X55 @ X54 @ X53)
% 1.30/1.52          | ~ (l1_orders_2 @ X54)
% 1.30/1.52          | ~ (v5_orders_2 @ X54)
% 1.30/1.52          | ~ (v4_orders_2 @ X54)
% 1.30/1.52          | ~ (v3_orders_2 @ X54)
% 1.30/1.52          | (v2_struct_0 @ X54))),
% 1.30/1.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 1.30/1.52  thf('101', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (v3_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v4_orders_2 @ sk_A)
% 1.30/1.52          | ~ (v5_orders_2 @ sk_A)
% 1.30/1.52          | ~ (l1_orders_2 @ sk_A)
% 1.30/1.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 1.30/1.52          | (r1_tarski @ X0 @ sk_C))),
% 1.30/1.52      inference('sup-', [status(thm)], ['99', '100'])).
% 1.30/1.52  thf('102', plain, ((v3_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('103', plain, ((v4_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('104', plain, ((v5_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('105', plain, ((l1_orders_2 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('106', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((v2_struct_0 @ sk_A)
% 1.30/1.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 1.30/1.52          | (r1_tarski @ X0 @ sk_C))),
% 1.30/1.52      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 1.30/1.52  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('108', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 1.30/1.52      inference('clc', [status(thm)], ['106', '107'])).
% 1.30/1.52  thf('109', plain,
% 1.30/1.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 1.30/1.52        | ((sk_C) = (sk_D))
% 1.30/1.52        | (v2_struct_0 @ sk_A)
% 1.30/1.52        | (r1_tarski @ sk_D @ sk_C))),
% 1.30/1.52      inference('sup-', [status(thm)], ['98', '108'])).
% 1.30/1.52  thf('110', plain,
% 1.30/1.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 1.30/1.52         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 1.30/1.52      inference('split', [status(esa)], ['2'])).
% 1.30/1.52  thf('111', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 1.30/1.52      inference('sat_resolution*', [status(thm)], ['3', '83'])).
% 1.30/1.52  thf('112', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 1.30/1.52      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 1.30/1.52  thf('113', plain,
% 1.30/1.52      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['109', '112'])).
% 1.30/1.52  thf('114', plain,
% 1.30/1.52      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 1.30/1.52      inference('split', [status(esa)], ['0'])).
% 1.30/1.52  thf('115', plain,
% 1.30/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 1.30/1.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.30/1.52  thf('116', plain,
% 1.30/1.52      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['114', '115'])).
% 1.30/1.52  thf('117', plain,
% 1.30/1.52      (![X6 : $i, X8 : $i]:
% 1.30/1.52         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.30/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.52  thf('118', plain,
% 1.30/1.52      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 1.30/1.52         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['116', '117'])).
% 1.30/1.52  thf('119', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 1.30/1.52      inference('sat_resolution*', [status(thm)], ['3', '83', '84'])).
% 1.30/1.52  thf('120', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 1.30/1.52      inference('simpl_trail', [status(thm)], ['118', '119'])).
% 1.30/1.52  thf('121', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 1.30/1.52      inference('clc', [status(thm)], ['113', '120'])).
% 1.30/1.52  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('123', plain, (((sk_C) = (sk_D))),
% 1.30/1.52      inference('clc', [status(thm)], ['121', '122'])).
% 1.30/1.52  thf('124', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 1.30/1.52      inference('demod', [status(thm)], ['86', '123'])).
% 1.30/1.52  thf(irreflexivity_r2_xboole_0, axiom,
% 1.30/1.52    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 1.30/1.52  thf('125', plain, (![X3 : $i]: ~ (r2_xboole_0 @ X3 @ X3)),
% 1.30/1.52      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 1.30/1.52  thf('126', plain, ($false), inference('sup-', [status(thm)], ['124', '125'])).
% 1.30/1.52  
% 1.30/1.52  % SZS output end Refutation
% 1.30/1.52  
% 1.30/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
