%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GVnmd4bFfO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:15 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  156 (1156 expanded)
%              Number of leaves         :   36 ( 341 expanded)
%              Depth                    :   26
%              Number of atoms          : 1179 (20896 expanded)
%              Number of equality atoms :   33 ( 108 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_orders_1 @ X25 @ ( k1_orders_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m2_orders_2 @ X26 @ X24 @ X25 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ X29 @ X27 )
      | ~ ( m1_orders_2 @ X29 @ X28 @ X27 )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X32 @ X31 @ X30 )
      | ~ ( m1_orders_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_orders_1 @ X33 @ ( k1_orders_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m2_orders_2 @ X35 @ X34 @ X33 )
      | ~ ( r1_xboole_0 @ X36 @ X35 )
      | ~ ( m2_orders_2 @ X36 @ X34 @ X33 )
      | ~ ( l1_orders_2 @ X34 )
      | ~ ( v5_orders_2 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v3_orders_2 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['50','74'])).

thf('76',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','75','76'])).

thf('78',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','77'])).

thf('79',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_orders_1 @ X37 @ ( k1_orders_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m2_orders_2 @ X39 @ X38 @ X37 )
      | ( m1_orders_2 @ X39 @ X38 @ X40 )
      | ( m1_orders_2 @ X40 @ X38 @ X39 )
      | ( X40 = X39 )
      | ~ ( m2_orders_2 @ X40 @ X38 @ X37 )
      | ~ ( l1_orders_2 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('83',plain,(
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
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('92',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ X29 @ X27 )
      | ~ ( m1_orders_2 @ X29 @ X28 @ X27 )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('103',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','75'])).

thf('104',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('108',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('109',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','75','76'])).

thf('112',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['78','115'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('117',plain,(
    ! [X3: $i] :
      ~ ( r2_xboole_0 @ X3 @ X3 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('118',plain,(
    $false ),
    inference('sup-',[status(thm)],['116','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GVnmd4bFfO
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 1068 iterations in 0.274s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.55/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.55/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.73  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.55/0.73  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.55/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.73  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.55/0.73  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.55/0.73  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.55/0.73  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.73  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.55/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.73  thf(t84_orders_2, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.55/0.73                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.73          ( ![B:$i]:
% 0.55/0.73            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73              ( ![C:$i]:
% 0.55/0.73                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.55/0.73                  ( ![D:$i]:
% 0.55/0.73                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.55/0.73                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.73      inference('split', [status(esa)], ['2'])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.55/0.73         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(dt_m2_orders_2, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.55/0.73         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.73       ( ![C:$i]:
% 0.55/0.73         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.55/0.73           ( ( v6_orders_2 @ C @ A ) & 
% 0.55/0.73             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.73         (~ (l1_orders_2 @ X24)
% 0.55/0.73          | ~ (v5_orders_2 @ X24)
% 0.55/0.73          | ~ (v4_orders_2 @ X24)
% 0.55/0.73          | ~ (v3_orders_2 @ X24)
% 0.55/0.73          | (v2_struct_0 @ X24)
% 0.55/0.73          | ~ (m1_orders_1 @ X25 @ (k1_orders_1 @ (u1_struct_0 @ X24)))
% 0.55/0.73          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.55/0.73          | ~ (m2_orders_2 @ X26 @ X24 @ X25))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73          | (v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (v3_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v4_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.73          | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.73  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73          | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.55/0.73  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.55/0.73      inference('clc', [status(thm)], ['13', '14'])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['5', '15'])).
% 0.55/0.73  thf(t67_orders_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.55/0.73  thf('17', plain,
% 0.55/0.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.55/0.73          | (r1_tarski @ X29 @ X27)
% 0.55/0.73          | ~ (m1_orders_2 @ X29 @ X28 @ X27)
% 0.55/0.73          | ~ (l1_orders_2 @ X28)
% 0.55/0.73          | ~ (v5_orders_2 @ X28)
% 0.55/0.73          | ~ (v4_orders_2 @ X28)
% 0.55/0.73          | ~ (v3_orders_2 @ X28)
% 0.55/0.73          | (v2_struct_0 @ X28))),
% 0.55/0.73      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (v3_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v4_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.73          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.73          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.55/0.73          | (r1_tarski @ X0 @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.73  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('23', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.55/0.73          | (r1_tarski @ X0 @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.55/0.73  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('25', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.55/0.73      inference('clc', [status(thm)], ['23', '24'])).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['4', '25'])).
% 0.55/0.73  thf(d8_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.55/0.73       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      (![X0 : $i, X2 : $i]:
% 0.55/0.73         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.73      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.55/0.73  thf('28', plain,
% 0.55/0.73      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.55/0.73         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.55/0.73      inference('split', [status(esa)], ['2'])).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      ((((sk_C) = (sk_D)))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.55/0.73         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('32', plain,
% 0.55/0.73      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('34', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.55/0.73      inference('clc', [status(thm)], ['13', '14'])).
% 0.55/0.73  thf('35', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.73  thf(t69_orders_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.55/0.73                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('37', plain,
% 0.55/0.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.55/0.73          | ((X30) = (k1_xboole_0))
% 0.55/0.73          | ~ (m1_orders_2 @ X32 @ X31 @ X30)
% 0.55/0.73          | ~ (m1_orders_2 @ X30 @ X31 @ X32)
% 0.55/0.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.55/0.73          | ~ (l1_orders_2 @ X31)
% 0.55/0.73          | ~ (v5_orders_2 @ X31)
% 0.55/0.73          | ~ (v4_orders_2 @ X31)
% 0.55/0.73          | ~ (v3_orders_2 @ X31)
% 0.55/0.73          | (v2_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (v3_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v4_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.73          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.55/0.73          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.55/0.73          | ((sk_C) = (k1_xboole_0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.73  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('43', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.55/0.73          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.55/0.73          | ((sk_C) = (k1_xboole_0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.55/0.73  thf('44', plain,
% 0.55/0.73      ((((sk_C) = (k1_xboole_0))
% 0.55/0.73        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.55/0.73        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.55/0.73        | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['35', '43'])).
% 0.55/0.73  thf('45', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_A)
% 0.55/0.73        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.55/0.73        | ((sk_C) = (k1_xboole_0)))),
% 0.55/0.73      inference('simplify', [status(thm)], ['44'])).
% 0.55/0.73  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('47', plain,
% 0.55/0.73      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.55/0.73      inference('clc', [status(thm)], ['45', '46'])).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      ((((sk_C) = (k1_xboole_0)))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['32', '47'])).
% 0.55/0.73  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('50', plain,
% 0.55/0.73      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['48', '49'])).
% 0.55/0.73  thf('51', plain,
% 0.55/0.73      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['48', '49'])).
% 0.55/0.73  thf('52', plain,
% 0.55/0.73      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t82_orders_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('53', plain,
% 0.55/0.73      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.55/0.73         (~ (m1_orders_1 @ X33 @ (k1_orders_1 @ (u1_struct_0 @ X34)))
% 0.55/0.73          | ~ (m2_orders_2 @ X35 @ X34 @ X33)
% 0.55/0.73          | ~ (r1_xboole_0 @ X36 @ X35)
% 0.55/0.73          | ~ (m2_orders_2 @ X36 @ X34 @ X33)
% 0.55/0.73          | ~ (l1_orders_2 @ X34)
% 0.55/0.73          | ~ (v5_orders_2 @ X34)
% 0.55/0.73          | ~ (v4_orders_2 @ X34)
% 0.55/0.73          | ~ (v3_orders_2 @ X34)
% 0.55/0.73          | (v2_struct_0 @ X34))),
% 0.55/0.73      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.55/0.73  thf('54', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (v3_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v4_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.73          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.73          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.55/0.73          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.73  thf('55', plain, ((v3_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('56', plain, ((v4_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('59', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.55/0.73          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.55/0.73  thf('60', plain,
% 0.55/0.73      ((![X0 : $i]:
% 0.55/0.73          (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73           | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.55/0.73           | (v2_struct_0 @ sk_A)))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['51', '59'])).
% 0.55/0.73  thf(t36_xboole_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.73  thf('61', plain,
% 0.55/0.73      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.55/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.73  thf(t79_xboole_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.55/0.73  thf('62', plain,
% 0.55/0.73      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.55/0.73      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.55/0.73  thf(symmetry_r1_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.55/0.73  thf('63', plain,
% 0.55/0.73      (![X4 : $i, X5 : $i]:
% 0.55/0.73         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.55/0.73      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.55/0.73  thf('64', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.55/0.73  thf(t83_xboole_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.73  thf('65', plain,
% 0.55/0.73      (![X18 : $i, X19 : $i]:
% 0.55/0.73         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.55/0.73      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.55/0.73  thf('66', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.73  thf(t38_xboole_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.55/0.73       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.55/0.73  thf('67', plain,
% 0.55/0.73      (![X11 : $i, X12 : $i]:
% 0.55/0.73         (((X11) = (k1_xboole_0))
% 0.55/0.73          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.55/0.73      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.55/0.73  thf('68', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.55/0.73          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.55/0.73  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['61', '68'])).
% 0.55/0.73  thf('70', plain,
% 0.55/0.73      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.55/0.73      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.55/0.73  thf('71', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.55/0.73      inference('sup+', [status(thm)], ['69', '70'])).
% 0.55/0.73  thf('72', plain,
% 0.55/0.73      ((![X0 : $i]: (~ (m2_orders_2 @ X0 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('demod', [status(thm)], ['60', '71'])).
% 0.55/0.73  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('74', plain,
% 0.55/0.73      ((![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))
% 0.55/0.73         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.55/0.73             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('clc', [status(thm)], ['72', '73'])).
% 0.55/0.73  thf('75', plain,
% 0.55/0.73      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['50', '74'])).
% 0.55/0.73  thf('76', plain,
% 0.55/0.73      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('77', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.73      inference('sat_resolution*', [status(thm)], ['3', '75', '76'])).
% 0.55/0.73  thf('78', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.55/0.73      inference('simpl_trail', [status(thm)], ['1', '77'])).
% 0.55/0.73  thf('79', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('80', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('81', plain,
% 0.55/0.73      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t83_orders_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.55/0.73                   ( ( ( C ) != ( D ) ) =>
% 0.55/0.73                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.55/0.73                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('82', plain,
% 0.55/0.73      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.55/0.73         (~ (m1_orders_1 @ X37 @ (k1_orders_1 @ (u1_struct_0 @ X38)))
% 0.55/0.73          | ~ (m2_orders_2 @ X39 @ X38 @ X37)
% 0.55/0.73          | (m1_orders_2 @ X39 @ X38 @ X40)
% 0.55/0.73          | (m1_orders_2 @ X40 @ X38 @ X39)
% 0.55/0.73          | ((X40) = (X39))
% 0.55/0.73          | ~ (m2_orders_2 @ X40 @ X38 @ X37)
% 0.55/0.73          | ~ (l1_orders_2 @ X38)
% 0.55/0.73          | ~ (v5_orders_2 @ X38)
% 0.55/0.73          | ~ (v4_orders_2 @ X38)
% 0.55/0.73          | ~ (v3_orders_2 @ X38)
% 0.55/0.73          | (v2_struct_0 @ X38))),
% 0.55/0.73      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.55/0.73  thf('83', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (v3_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v4_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.73          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.73          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73          | ((X0) = (X1))
% 0.55/0.73          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.55/0.73          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.55/0.73          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['81', '82'])).
% 0.55/0.73  thf('84', plain, ((v3_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('85', plain, ((v4_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('86', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('88', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73          | ((X0) = (X1))
% 0.55/0.73          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.55/0.73          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.55/0.73          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.55/0.73  thf('89', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.55/0.73          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.55/0.73          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.55/0.73          | ((sk_C) = (X0))
% 0.55/0.73          | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['80', '88'])).
% 0.55/0.73  thf('90', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_A)
% 0.55/0.73        | ((sk_C) = (sk_D))
% 0.55/0.73        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.55/0.73        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['79', '89'])).
% 0.55/0.73  thf('91', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.55/0.73  thf('92', plain,
% 0.55/0.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.55/0.73          | (r1_tarski @ X29 @ X27)
% 0.55/0.73          | ~ (m1_orders_2 @ X29 @ X28 @ X27)
% 0.55/0.73          | ~ (l1_orders_2 @ X28)
% 0.55/0.73          | ~ (v5_orders_2 @ X28)
% 0.55/0.73          | ~ (v4_orders_2 @ X28)
% 0.55/0.73          | ~ (v3_orders_2 @ X28)
% 0.55/0.73          | (v2_struct_0 @ X28))),
% 0.55/0.73      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.55/0.73  thf('93', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (v3_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v4_orders_2 @ sk_A)
% 0.55/0.73          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.73          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.73          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.55/0.73          | (r1_tarski @ X0 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['91', '92'])).
% 0.55/0.73  thf('94', plain, ((v3_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('95', plain, ((v4_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('97', plain, ((l1_orders_2 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('98', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v2_struct_0 @ sk_A)
% 0.55/0.73          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.55/0.73          | (r1_tarski @ X0 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.55/0.73  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('100', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.55/0.73      inference('clc', [status(thm)], ['98', '99'])).
% 0.55/0.73  thf('101', plain,
% 0.55/0.73      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.55/0.73        | ((sk_C) = (sk_D))
% 0.55/0.73        | (v2_struct_0 @ sk_A)
% 0.55/0.73        | (r1_tarski @ sk_D @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['90', '100'])).
% 0.55/0.73  thf('102', plain,
% 0.55/0.73      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.55/0.73         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.55/0.73      inference('split', [status(esa)], ['2'])).
% 0.55/0.73  thf('103', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.55/0.73      inference('sat_resolution*', [status(thm)], ['3', '75'])).
% 0.55/0.73  thf('104', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.55/0.73      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 0.55/0.73  thf('105', plain,
% 0.55/0.73      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['101', '104'])).
% 0.55/0.73  thf('106', plain,
% 0.55/0.73      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('107', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.55/0.73      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.55/0.73  thf('108', plain,
% 0.55/0.73      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['106', '107'])).
% 0.55/0.73  thf(d10_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.73  thf('109', plain,
% 0.55/0.73      (![X6 : $i, X8 : $i]:
% 0.55/0.73         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.55/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.73  thf('110', plain,
% 0.55/0.73      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.55/0.73         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['108', '109'])).
% 0.55/0.73  thf('111', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.73      inference('sat_resolution*', [status(thm)], ['3', '75', '76'])).
% 0.55/0.73  thf('112', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.55/0.73      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.55/0.73  thf('113', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('clc', [status(thm)], ['105', '112'])).
% 0.55/0.73  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('115', plain, (((sk_C) = (sk_D))),
% 0.55/0.73      inference('clc', [status(thm)], ['113', '114'])).
% 0.55/0.73  thf('116', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['78', '115'])).
% 0.55/0.73  thf(irreflexivity_r2_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.55/0.73  thf('117', plain, (![X3 : $i]: ~ (r2_xboole_0 @ X3 @ X3)),
% 0.55/0.73      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.55/0.73  thf('118', plain, ($false), inference('sup-', [status(thm)], ['116', '117'])).
% 0.55/0.73  
% 0.55/0.73  % SZS output end Refutation
% 0.55/0.73  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
