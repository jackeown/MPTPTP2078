%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GIYzsn4m5R

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 593 expanded)
%              Number of leaves         :   32 ( 182 expanded)
%              Depth                    :   23
%              Number of atoms          : 1014 (10441 expanded)
%              Number of equality atoms :   26 (  50 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_orders_1 @ X10 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m2_orders_2 @ X11 @ X9 @ X10 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_orders_2 @ X14 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf(t68_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( ( B != k1_xboole_0 )
                & ( m1_orders_2 @ B @ A @ B ) )
            & ~ ( ~ ( m1_orders_2 @ B @ A @ B )
                & ( B = k1_xboole_0 ) ) ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_orders_2 @ X15 @ X16 @ X15 )
      | ( X15 = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t68_orders_2])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ ( u1_struct_0 @ X18 ) ) @ X19 )
      | ~ ( m2_orders_2 @ X19 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['46','56'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('59',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('61',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','62','63'])).

thf('65',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','64'])).

thf('66',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m2_orders_2 @ X22 @ X21 @ X20 )
      | ( m1_orders_2 @ X22 @ X21 @ X23 )
      | ( m1_orders_2 @ X23 @ X21 @ X22 )
      | ( X23 = X22 )
      | ~ ( m2_orders_2 @ X23 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('70',plain,(
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['66','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('79',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_orders_2 @ X14 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('90',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','62'])).

thf('91',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('95',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','62','63'])).

thf('99',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['92','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['65','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('105',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    $false ),
    inference('sup-',[status(thm)],['103','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GIYzsn4m5R
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 104 iterations in 0.045s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.51  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.51  thf(t84_orders_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.51                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.51                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.51         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m2_orders_2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.51         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.51           ( ( v6_orders_2 @ C @ A ) & 
% 0.20/0.51             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (l1_orders_2 @ X9)
% 0.20/0.51          | ~ (v5_orders_2 @ X9)
% 0.20/0.51          | ~ (v4_orders_2 @ X9)
% 0.20/0.51          | ~ (v3_orders_2 @ X9)
% 0.20/0.51          | (v2_struct_0 @ X9)
% 0.20/0.51          | ~ (m1_orders_1 @ X10 @ (k1_orders_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | ~ (m2_orders_2 @ X11 @ X9 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.51  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '15'])).
% 0.20/0.51  thf(t67_orders_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | (r1_tarski @ X14 @ X12)
% 0.20/0.51          | ~ (m1_orders_2 @ X14 @ X13 @ X12)
% 0.20/0.51          | ~ (l1_orders_2 @ X13)
% 0.20/0.51          | ~ (v5_orders_2 @ X13)
% 0.20/0.51          | ~ (v4_orders_2 @ X13)
% 0.20/0.51          | ~ (v3_orders_2 @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.51          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.51          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.20/0.51  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '25'])).
% 0.20/0.51  thf(d8_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.20/0.51         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((sk_C) = (sk_D)))
% 0.20/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.51         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.20/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf(t68_orders_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.20/0.51             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.20/0.51                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.51          | ~ (m1_orders_2 @ X15 @ X16 @ X15)
% 0.20/0.51          | ((X15) = (k1_xboole_0))
% 0.20/0.51          | ~ (l1_orders_2 @ X16)
% 0.20/0.51          | ~ (v5_orders_2 @ X16)
% 0.20/0.51          | ~ (v4_orders_2 @ X16)
% 0.20/0.51          | ~ (v3_orders_2 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t68_orders_2])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51        | ((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.20/0.51  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '44'])).
% 0.20/0.51  thf('46', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t79_orders_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.51               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X17 @ (u1_struct_0 @ X18)) @ X19)
% 0.20/0.51          | ~ (m2_orders_2 @ X19 @ X18 @ X17)
% 0.20/0.51          | ~ (l1_orders_2 @ X18)
% 0.20/0.51          | ~ (v5_orders_2 @ X18)
% 0.20/0.51          | ~ (v4_orders_2 @ X18)
% 0.20/0.51          | ~ (v3_orders_2 @ X18)
% 0.20/0.51          | (v2_struct_0 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('51', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.20/0.51  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '56'])).
% 0.20/0.51  thf(t7_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (~ (r1_tarski @ sk_C @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((~ (r1_tarski @ k1_xboole_0 @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.51             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '59'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('61', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('64', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '62', '63'])).
% 0.20/0.51  thf('65', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['1', '64'])).
% 0.20/0.51  thf('66', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t83_orders_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.51                   ( ( ( C ) != ( D ) ) =>
% 0.20/0.51                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.20/0.51                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         (~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X21)))
% 0.20/0.51          | ~ (m2_orders_2 @ X22 @ X21 @ X20)
% 0.20/0.51          | (m1_orders_2 @ X22 @ X21 @ X23)
% 0.20/0.51          | (m1_orders_2 @ X23 @ X21 @ X22)
% 0.20/0.51          | ((X23) = (X22))
% 0.20/0.51          | ~ (m2_orders_2 @ X23 @ X21 @ X20)
% 0.20/0.51          | ~ (l1_orders_2 @ X21)
% 0.20/0.51          | ~ (v5_orders_2 @ X21)
% 0.20/0.51          | ~ (v4_orders_2 @ X21)
% 0.20/0.51          | ~ (v3_orders_2 @ X21)
% 0.20/0.51          | (v2_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.51          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.51          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('74', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | ((X0) = (X1))
% 0.20/0.51          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.51          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.51          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.51          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.20/0.51          | ((sk_C) = (X0))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['67', '75'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((sk_C) = (sk_D))
% 0.20/0.51        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.20/0.51        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['66', '76'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | (r1_tarski @ X14 @ X12)
% 0.20/0.51          | ~ (m1_orders_2 @ X14 @ X13 @ X12)
% 0.20/0.51          | ~ (l1_orders_2 @ X13)
% 0.20/0.51          | ~ (v5_orders_2 @ X13)
% 0.20/0.51          | ~ (v4_orders_2 @ X13)
% 0.20/0.51          | ~ (v3_orders_2 @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.51          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.51          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('82', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('83', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.51          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.20/0.51  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['85', '86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.20/0.51        | ((sk_C) = (sk_D))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (r1_tarski @ sk_D @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['77', '87'])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.51         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('90', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '62'])).
% 0.20/0.51  thf('91', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['88', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.20/0.51         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.51  thf('98', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '62', '63'])).
% 0.20/0.51  thf('99', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 0.20/0.51  thf('100', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['92', '99'])).
% 0.20/0.51  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain, (((sk_C) = (sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.51  thf('103', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['65', '102'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('105', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.20/0.51      inference('simplify', [status(thm)], ['104'])).
% 0.20/0.51  thf('106', plain, ($false), inference('sup-', [status(thm)], ['103', '105'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
