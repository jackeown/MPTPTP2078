%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ddkyyFsnAH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:14 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 702 expanded)
%              Number of leaves         :   34 ( 213 expanded)
%              Depth                    :   23
%              Number of atoms          : 1098 (12307 expanded)
%              Number of equality atoms :   28 (  59 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('50',plain,(
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

thf('51',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_orders_1 @ X24 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ ( u1_struct_0 @ X25 ) ) @ X26 )
      | ~ ( m2_orders_2 @ X26 @ X25 @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['49','59'])).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','67'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','70','71'])).

thf('73',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','72'])).

thf('74',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
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

thf('77',plain,(
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

thf('78',plain,(
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
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['85','95'])).

thf('97',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','70'])).

thf('99',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('103',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','70','71'])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['100','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['73','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('113',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    $false ),
    inference('sup-',[status(thm)],['111','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ddkyyFsnAH
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 170 iterations in 0.067s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.37/0.55  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.37/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.37/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.55  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.37/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(t84_orders_2, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.37/0.55               ( ![D:$i]:
% 0.37/0.55                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.37/0.55                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.55            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55              ( ![C:$i]:
% 0.37/0.55                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.37/0.55                  ( ![D:$i]:
% 0.37/0.55                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.37/0.55                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.37/0.55         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_m2_orders_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.37/0.55         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.37/0.55           ( ( v6_orders_2 @ C @ A ) & 
% 0.37/0.55             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         (~ (l1_orders_2 @ X15)
% 0.37/0.55          | ~ (v5_orders_2 @ X15)
% 0.37/0.55          | ~ (v4_orders_2 @ X15)
% 0.37/0.55          | ~ (v3_orders_2 @ X15)
% 0.37/0.55          | (v2_struct_0 @ X15)
% 0.37/0.55          | ~ (m1_orders_1 @ X16 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.37/0.55          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.55          | ~ (m2_orders_2 @ X17 @ X15 @ X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.55          | ~ (l1_orders_2 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.37/0.55  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '15'])).
% 0.37/0.55  thf(t67_orders_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.55          | (r1_tarski @ X20 @ X18)
% 0.37/0.55          | ~ (m1_orders_2 @ X20 @ X19 @ X18)
% 0.37/0.55          | ~ (l1_orders_2 @ X19)
% 0.37/0.55          | ~ (v5_orders_2 @ X19)
% 0.37/0.55          | ~ (v4_orders_2 @ X19)
% 0.37/0.55          | ~ (v3_orders_2 @ X19)
% 0.37/0.55          | (v2_struct_0 @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.55          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.37/0.55          | (r1_tarski @ X0 @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.37/0.55          | (r1_tarski @ X0 @ sk_D))),
% 0.37/0.55      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.37/0.55  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.37/0.55      inference('clc', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '25'])).
% 0.37/0.55  thf(d8_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.55       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i]:
% 0.37/0.55         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.37/0.55         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((((sk_C) = (sk_D)))
% 0.37/0.55         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.37/0.55             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.37/0.55         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.37/0.55         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.37/0.55             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf('33', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf(t69_orders_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.37/0.55          | ((X21) = (k1_xboole_0))
% 0.37/0.55          | ~ (m1_orders_2 @ X23 @ X22 @ X21)
% 0.37/0.55          | ~ (m1_orders_2 @ X21 @ X22 @ X23)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.37/0.55          | ~ (l1_orders_2 @ X22)
% 0.37/0.55          | ~ (v5_orders_2 @ X22)
% 0.37/0.55          | ~ (v4_orders_2 @ X22)
% 0.37/0.55          | ~ (v3_orders_2 @ X22)
% 0.37/0.55          | (v2_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.37/0.55          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.55          | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.37/0.55          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.55          | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      ((((sk_C) = (k1_xboole_0))
% 0.37/0.55        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.37/0.55        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.37/0.55        | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['35', '43'])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_A)
% 0.37/0.55        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.37/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.55  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.37/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      ((((sk_C) = (k1_xboole_0)))
% 0.37/0.55         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.37/0.55             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '47'])).
% 0.37/0.55  thf('49', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t79_orders_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.37/0.55               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.55         (~ (m1_orders_1 @ X24 @ (k1_orders_1 @ (u1_struct_0 @ X25)))
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ X24 @ (u1_struct_0 @ X25)) @ X26)
% 0.37/0.55          | ~ (m2_orders_2 @ X26 @ X25 @ X24)
% 0.37/0.55          | ~ (l1_orders_2 @ X25)
% 0.37/0.55          | ~ (v5_orders_2 @ X25)
% 0.37/0.55          | ~ (v4_orders_2 @ X25)
% 0.37/0.55          | ~ (v3_orders_2 @ X25)
% 0.37/0.55          | (v2_struct_0 @ X25))),
% 0.37/0.55      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.55  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.55          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.37/0.55  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.37/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('clc', [status(thm)], ['57', '58'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '59'])).
% 0.37/0.55  thf(d10_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('62', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.37/0.55      inference('simplify', [status(thm)], ['61'])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X6 : $i, X8 : $i]:
% 0.37/0.55         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('64', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.55  thf(t5_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X9 @ X10)
% 0.37/0.55          | ~ (v1_xboole_0 @ X11)
% 0.37/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.37/0.55  thf('67', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['60', '66'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.37/0.55         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.37/0.55             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '67'])).
% 0.37/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.55  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('70', plain,
% 0.37/0.55      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.37/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.37/0.55  thf('71', plain,
% 0.37/0.55      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('72', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['3', '70', '71'])).
% 0.37/0.55  thf('73', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['1', '72'])).
% 0.37/0.55  thf('74', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('75', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t83_orders_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.37/0.55               ( ![D:$i]:
% 0.37/0.55                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.37/0.55                   ( ( ( C ) != ( D ) ) =>
% 0.37/0.55                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.37/0.55                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.55         (~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X28)))
% 0.37/0.55          | ~ (m2_orders_2 @ X29 @ X28 @ X27)
% 0.37/0.55          | (m1_orders_2 @ X29 @ X28 @ X30)
% 0.37/0.55          | (m1_orders_2 @ X30 @ X28 @ X29)
% 0.37/0.55          | ((X30) = (X29))
% 0.37/0.55          | ~ (m2_orders_2 @ X30 @ X28 @ X27)
% 0.37/0.55          | ~ (l1_orders_2 @ X28)
% 0.37/0.55          | ~ (v5_orders_2 @ X28)
% 0.37/0.55          | ~ (v4_orders_2 @ X28)
% 0.37/0.55          | ~ (v3_orders_2 @ X28)
% 0.37/0.55          | (v2_struct_0 @ X28))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.37/0.55  thf('78', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.55          | ((X0) = (X1))
% 0.37/0.55          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.37/0.55          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.37/0.55          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.37/0.55  thf('79', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('80', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('81', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('83', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.55          | ((X0) = (X1))
% 0.37/0.55          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.37/0.55          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.37/0.55          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.37/0.55  thf('84', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.37/0.55          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.55          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.37/0.55          | ((sk_C) = (X0))
% 0.37/0.55          | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '83'])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_A)
% 0.37/0.55        | ((sk_C) = (sk_D))
% 0.37/0.55        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.37/0.55        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['74', '84'])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('87', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.55          | (r1_tarski @ X20 @ X18)
% 0.37/0.55          | ~ (m1_orders_2 @ X20 @ X19 @ X18)
% 0.37/0.55          | ~ (l1_orders_2 @ X19)
% 0.37/0.55          | ~ (v5_orders_2 @ X19)
% 0.37/0.55          | ~ (v4_orders_2 @ X19)
% 0.37/0.55          | ~ (v3_orders_2 @ X19)
% 0.37/0.55          | (v2_struct_0 @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.37/0.55  thf('88', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.55          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.55          | (r1_tarski @ X0 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['86', '87'])).
% 0.37/0.55  thf('89', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('90', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('91', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('93', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.37/0.55          | (r1_tarski @ X0 @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.37/0.55  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('95', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.37/0.55      inference('clc', [status(thm)], ['93', '94'])).
% 0.37/0.55  thf('96', plain,
% 0.37/0.55      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.37/0.55        | ((sk_C) = (sk_D))
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (r1_tarski @ sk_D @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['85', '95'])).
% 0.37/0.55  thf('97', plain,
% 0.37/0.55      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.37/0.55         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('98', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['3', '70'])).
% 0.37/0.55  thf('99', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 0.37/0.55  thf('100', plain,
% 0.37/0.55      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['96', '99'])).
% 0.37/0.55  thf('101', plain,
% 0.37/0.55      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('102', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.55  thf('103', plain,
% 0.37/0.55      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.37/0.55  thf('104', plain,
% 0.37/0.55      (![X3 : $i, X5 : $i]:
% 0.37/0.55         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('105', plain,
% 0.37/0.55      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.37/0.55         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['103', '104'])).
% 0.37/0.55  thf('106', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['3', '70', '71'])).
% 0.37/0.55  thf('107', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.37/0.55  thf('108', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['100', '107'])).
% 0.37/0.55  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('110', plain, (((sk_C) = (sk_D))),
% 0.37/0.55      inference('clc', [status(thm)], ['108', '109'])).
% 0.37/0.55  thf('111', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.37/0.55      inference('demod', [status(thm)], ['73', '110'])).
% 0.37/0.55  thf('112', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.55  thf('113', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.37/0.55      inference('simplify', [status(thm)], ['112'])).
% 0.37/0.55  thf('114', plain, ($false), inference('sup-', [status(thm)], ['111', '113'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
