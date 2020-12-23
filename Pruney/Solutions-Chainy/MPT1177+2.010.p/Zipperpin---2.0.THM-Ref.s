%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CL3rMYY9L2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:13 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 654 expanded)
%              Number of leaves         :   34 ( 201 expanded)
%              Depth                    :   25
%              Number of atoms          : 1118 (10912 expanded)
%              Number of equality atoms :   31 (  71 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ~ ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ~ ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X14 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_orders_2 @ X18 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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
    ( ( r1_tarski @ sk_C_1 @ sk_D )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,
    ( ( ( sk_C_1 = sk_D )
      | ( r2_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
   <= ~ ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( sk_C_1 = sk_D )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_orders_2 @ X19 @ X20 @ X19 )
      | ( X19 = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t68_orders_2])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 ) ),
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
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_orders_1 @ X21 @ ( k1_orders_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ ( u1_struct_0 @ X22 ) ) @ X23 )
      | ~ ( m2_orders_2 @ X23 @ X22 @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('60',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('61',plain,(
    ! [X10: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X10 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['60','73'])).

thf('75',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','74','75'])).

thf('77',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','76'])).

thf('78',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_orders_1 @ X24 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m2_orders_2 @ X26 @ X25 @ X24 )
      | ( m1_orders_2 @ X26 @ X25 @ X27 )
      | ( m1_orders_2 @ X27 @ X25 @ X26 )
      | ( X27 = X26 )
      | ~ ( m2_orders_2 @ X27 @ X25 @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('82',plain,(
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
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( m1_orders_2 @ sk_C_1 @ sk_A @ X0 )
      | ( sk_C_1 = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('91',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ X18 @ X16 )
      | ~ ( m1_orders_2 @ X18 @ X17 @ X16 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['89','99'])).

thf('101',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('102',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','74'])).

thf('103',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('107',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_D )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
      | ( sk_D = sk_C_1 ) )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','74','75'])).

thf('111',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ( sk_D = sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_C_1 = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['104','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    sk_C_1 = sk_D ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['77','114'])).

thf('116',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 != X5 )
      | ~ ( r2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('117',plain,(
    ! [X5: $i] :
      ~ ( r2_xboole_0 @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    $false ),
    inference('sup-',[status(thm)],['115','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CL3rMYY9L2
% 0.13/0.36  % Computer   : n011.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:38:42 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 136 iterations in 0.054s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.35/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.53  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.35/0.53  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.35/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.35/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.35/0.53  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.35/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(t84_orders_2, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.53               ( ![D:$i]:
% 0.35/0.53                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.35/0.53                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53              ( ![C:$i]:
% 0.35/0.53                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.53                  ( ![D:$i]:
% 0.35/0.53                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.35/0.53                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (((r2_xboole_0 @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.35/0.53        | ~ (r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)) | 
% 0.35/0.53       ~ ((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.35/0.53      inference('split', [status(esa)], ['2'])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.35/0.53         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_m2_orders_2, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.35/0.53         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.53       ( ![C:$i]:
% 0.35/0.53         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.53           ( ( v6_orders_2 @ C @ A ) & 
% 0.35/0.53             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.53         (~ (l1_orders_2 @ X13)
% 0.35/0.53          | ~ (v5_orders_2 @ X13)
% 0.35/0.53          | ~ (v4_orders_2 @ X13)
% 0.35/0.53          | ~ (v3_orders_2 @ X13)
% 0.35/0.53          | (v2_struct_0 @ X13)
% 0.35/0.53          | ~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.35/0.53          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.53          | ~ (m2_orders_2 @ X15 @ X13 @ X14))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | (v2_struct_0 @ sk_A)
% 0.35/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.53          | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.53  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.35/0.53  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '15'])).
% 0.35/0.53  thf(t67_orders_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.53          | (r1_tarski @ X18 @ X16)
% 0.35/0.53          | ~ (m1_orders_2 @ X18 @ X17 @ X16)
% 0.35/0.53          | ~ (l1_orders_2 @ X17)
% 0.35/0.53          | ~ (v5_orders_2 @ X17)
% 0.35/0.53          | ~ (v4_orders_2 @ X17)
% 0.35/0.53          | ~ (v3_orders_2 @ X17)
% 0.35/0.53          | (v2_struct_0 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ sk_A)
% 0.35/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.35/0.53          | (r1_tarski @ X0 @ sk_D))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ sk_A)
% 0.35/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.35/0.53          | (r1_tarski @ X0 @ sk_D))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.35/0.53  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.35/0.53      inference('clc', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (((r1_tarski @ sk_C_1 @ sk_D))
% 0.35/0.53         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['4', '25'])).
% 0.35/0.53  thf(d8_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.35/0.53       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X4 : $i, X6 : $i]:
% 0.35/0.53         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (((((sk_C_1) = (sk_D)) | (r2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.35/0.53         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      ((~ (r2_xboole_0 @ sk_C_1 @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.35/0.53      inference('split', [status(esa)], ['2'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      ((((sk_C_1) = (sk_D)))
% 0.35/0.53         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.35/0.53             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.35/0.53         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))
% 0.35/0.53         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.35/0.53             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.35/0.53  thf('33', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.35/0.53      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf(t68_orders_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.35/0.53             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.35/0.53                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (![X19 : $i, X20 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.35/0.53          | ~ (m1_orders_2 @ X19 @ X20 @ X19)
% 0.35/0.53          | ((X19) = (k1_xboole_0))
% 0.35/0.53          | ~ (l1_orders_2 @ X20)
% 0.35/0.53          | ~ (v5_orders_2 @ X20)
% 0.35/0.53          | ~ (v4_orders_2 @ X20)
% 0.35/0.53          | ~ (v3_orders_2 @ X20)
% 0.35/0.53          | (v2_struct_0 @ X20))),
% 0.35/0.53      inference('cnf', [status(esa)], [t68_orders_2])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.35/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.35/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.35/0.53        | ~ (l1_orders_2 @ sk_A)
% 0.35/0.53        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.53        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.53  thf('38', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('39', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A)
% 0.35/0.53        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.53        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.35/0.53  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.53      inference('clc', [status(thm)], ['42', '43'])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      ((((sk_C_1) = (k1_xboole_0)))
% 0.35/0.53         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.35/0.53             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['32', '44'])).
% 0.35/0.53  thf('46', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.35/0.53         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.35/0.53             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['45', '46'])).
% 0.35/0.53  thf('48', plain,
% 0.35/0.53      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t79_orders_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.53               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.53         (~ (m1_orders_1 @ X21 @ (k1_orders_1 @ (u1_struct_0 @ X22)))
% 0.35/0.53          | (r2_hidden @ (k1_funct_1 @ X21 @ (u1_struct_0 @ X22)) @ X23)
% 0.35/0.53          | ~ (m2_orders_2 @ X23 @ X22 @ X21)
% 0.35/0.53          | ~ (l1_orders_2 @ X22)
% 0.35/0.53          | ~ (v5_orders_2 @ X22)
% 0.35/0.53          | ~ (v4_orders_2 @ X22)
% 0.35/0.53          | ~ (v3_orders_2 @ X22)
% 0.35/0.53          | (v2_struct_0 @ X22))),
% 0.35/0.53      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ sk_A)
% 0.35/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.53          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.54  thf('51', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('52', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('53', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.54          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.35/0.54  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.35/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.35/0.54      inference('clc', [status(thm)], ['55', '56'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      (((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ k1_xboole_0))
% 0.35/0.54         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.35/0.54             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['47', '57'])).
% 0.35/0.54  thf(t7_ordinal1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      ((~ (r1_tarski @ k1_xboole_0 @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.35/0.54         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.35/0.54             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.35/0.54  thf(t61_xboole_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      (![X10 : $i]:
% 0.35/0.54         ((r2_xboole_0 @ k1_xboole_0 @ X10) | ((X10) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.35/0.54  thf('62', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ~ (r2_xboole_0 @ X4 @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.54  thf('63', plain,
% 0.35/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.35/0.54  thf(d3_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      (![X1 : $i, X3 : $i]:
% 0.35/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.54  thf('65', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.54          | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['63', '66'])).
% 0.35/0.54  thf('68', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.35/0.54  thf('69', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.35/0.54          | (r1_tarski @ k1_xboole_0 @ X0)
% 0.35/0.54          | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.35/0.54  thf(d10_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('70', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.54  thf('71', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.35/0.54      inference('simplify', [status(thm)], ['70'])).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r1_tarski @ k1_xboole_0 @ X0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['69', '71'])).
% 0.35/0.54  thf('73', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.54      inference('simplify', [status(thm)], ['72'])).
% 0.35/0.54  thf('74', plain,
% 0.35/0.54      (((r2_xboole_0 @ sk_C_1 @ sk_D)) | 
% 0.35/0.54       ~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['60', '73'])).
% 0.35/0.54  thf('75', plain,
% 0.35/0.54      (((r2_xboole_0 @ sk_C_1 @ sk_D)) | ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('76', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['3', '74', '75'])).
% 0.35/0.54  thf('77', plain, ((r2_xboole_0 @ sk_C_1 @ sk_D)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['1', '76'])).
% 0.35/0.54  thf('78', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('79', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('80', plain,
% 0.35/0.54      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t83_orders_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ![C:$i]:
% 0.35/0.54             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.35/0.54               ( ![D:$i]:
% 0.35/0.54                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.35/0.54                   ( ( ( C ) != ( D ) ) =>
% 0.35/0.54                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.35/0.54                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('81', plain,
% 0.35/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.54         (~ (m1_orders_1 @ X24 @ (k1_orders_1 @ (u1_struct_0 @ X25)))
% 0.35/0.54          | ~ (m2_orders_2 @ X26 @ X25 @ X24)
% 0.35/0.54          | (m1_orders_2 @ X26 @ X25 @ X27)
% 0.35/0.54          | (m1_orders_2 @ X27 @ X25 @ X26)
% 0.35/0.54          | ((X27) = (X26))
% 0.35/0.54          | ~ (m2_orders_2 @ X27 @ X25 @ X24)
% 0.35/0.54          | ~ (l1_orders_2 @ X25)
% 0.35/0.54          | ~ (v5_orders_2 @ X25)
% 0.35/0.54          | ~ (v4_orders_2 @ X25)
% 0.35/0.54          | ~ (v3_orders_2 @ X25)
% 0.35/0.54          | (v2_struct_0 @ X25))),
% 0.35/0.54      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.35/0.54  thf('82', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.54          | ((X0) = (X1))
% 0.35/0.54          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.35/0.54          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.35/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['80', '81'])).
% 0.35/0.54  thf('83', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('84', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('85', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('87', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.54          | ((X0) = (X1))
% 0.35/0.54          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.35/0.54          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.35/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.35/0.54  thf('88', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.54          | (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.35/0.54          | (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.54          | ((sk_C_1) = (X0))
% 0.35/0.54          | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['79', '87'])).
% 0.35/0.54  thf('89', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | ((sk_C_1) = (sk_D))
% 0.35/0.54        | (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.35/0.54        | (m1_orders_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['78', '88'])).
% 0.35/0.54  thf('90', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.54  thf('91', plain,
% 0.35/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.54          | (r1_tarski @ X18 @ X16)
% 0.35/0.54          | ~ (m1_orders_2 @ X18 @ X17 @ X16)
% 0.35/0.54          | ~ (l1_orders_2 @ X17)
% 0.35/0.54          | ~ (v5_orders_2 @ X17)
% 0.35/0.54          | ~ (v4_orders_2 @ X17)
% 0.35/0.54          | ~ (v3_orders_2 @ X17)
% 0.35/0.54          | (v2_struct_0 @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.35/0.54  thf('92', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.35/0.54          | (r1_tarski @ X0 @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['90', '91'])).
% 0.35/0.54  thf('93', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('94', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('95', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('96', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('97', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ sk_A)
% 0.35/0.54          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.35/0.54          | (r1_tarski @ X0 @ sk_C_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.35/0.54  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('99', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r1_tarski @ X0 @ sk_C_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1))),
% 0.35/0.54      inference('clc', [status(thm)], ['97', '98'])).
% 0.35/0.54  thf('100', plain,
% 0.35/0.54      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.35/0.54        | ((sk_C_1) = (sk_D))
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | (r1_tarski @ sk_D @ sk_C_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['89', '99'])).
% 0.35/0.54  thf('101', plain,
% 0.35/0.54      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.35/0.54         <= (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.35/0.54      inference('split', [status(esa)], ['2'])).
% 0.35/0.54  thf('102', plain, (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['3', '74'])).
% 0.35/0.54  thf('103', plain, (~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['101', '102'])).
% 0.35/0.54  thf('104', plain,
% 0.35/0.54      (((r1_tarski @ sk_D @ sk_C_1)
% 0.35/0.54        | (v2_struct_0 @ sk_A)
% 0.35/0.54        | ((sk_C_1) = (sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['100', '103'])).
% 0.35/0.54  thf('105', plain,
% 0.35/0.54      (((r2_xboole_0 @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('106', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ~ (r2_xboole_0 @ X4 @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.54  thf('107', plain,
% 0.35/0.54      (((r1_tarski @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['105', '106'])).
% 0.35/0.54  thf('108', plain,
% 0.35/0.54      (![X7 : $i, X9 : $i]:
% 0.35/0.54         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.35/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.54  thf('109', plain,
% 0.35/0.54      (((~ (r1_tarski @ sk_D @ sk_C_1) | ((sk_D) = (sk_C_1))))
% 0.35/0.54         <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['107', '108'])).
% 0.35/0.54  thf('110', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['3', '74', '75'])).
% 0.35/0.54  thf('111', plain, ((~ (r1_tarski @ sk_D @ sk_C_1) | ((sk_D) = (sk_C_1)))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 0.35/0.54  thf('112', plain, ((((sk_C_1) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('clc', [status(thm)], ['104', '111'])).
% 0.35/0.54  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('114', plain, (((sk_C_1) = (sk_D))),
% 0.35/0.54      inference('clc', [status(thm)], ['112', '113'])).
% 0.35/0.54  thf('115', plain, ((r2_xboole_0 @ sk_C_1 @ sk_C_1)),
% 0.35/0.54      inference('demod', [status(thm)], ['77', '114'])).
% 0.35/0.54  thf('116', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]: (((X4) != (X5)) | ~ (r2_xboole_0 @ X4 @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.54  thf('117', plain, (![X5 : $i]: ~ (r2_xboole_0 @ X5 @ X5)),
% 0.35/0.54      inference('simplify', [status(thm)], ['116'])).
% 0.35/0.54  thf('118', plain, ($false), inference('sup-', [status(thm)], ['115', '117'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
