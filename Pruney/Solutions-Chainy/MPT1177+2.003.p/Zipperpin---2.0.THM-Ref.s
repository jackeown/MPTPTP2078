%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HosLCXpFns

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 703 expanded)
%              Number of leaves         :   35 ( 214 expanded)
%              Depth                    :   23
%              Number of atoms          : 1100 (12466 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m2_orders_2 @ X18 @ X16 @ X17 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ X21 @ X19 )
      | ~ ( m1_orders_2 @ X21 @ X20 @ X19 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_orders_2 @ X22 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
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
      | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_orders_1 @ X25 @ ( k1_orders_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m2_orders_2 @ X27 @ X26 @ X25 )
      | ~ ( r1_xboole_0 @ X28 @ X27 )
      | ~ ( m2_orders_2 @ X28 @ X26 @ X25 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( r1_xboole_0 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','69','70'])).

thf('72',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','71'])).

thf('73',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_orders_1 @ X29 @ ( k1_orders_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m2_orders_2 @ X31 @ X30 @ X29 )
      | ( m1_orders_2 @ X31 @ X30 @ X32 )
      | ( m1_orders_2 @ X32 @ X30 @ X31 )
      | ( X32 = X31 )
      | ~ ( m2_orders_2 @ X32 @ X30 @ X29 )
      | ~ ( l1_orders_2 @ X30 )
      | ~ ( v5_orders_2 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v3_orders_2 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('77',plain,(
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
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( m1_orders_2 @ sk_D @ sk_A @ X0 )
      | ( sk_D = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_C_1 )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ X21 @ X19 )
      | ~ ( m1_orders_2 @ X21 @ X20 @ X19 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ( sk_D = sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['84','94'])).

thf('96',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('97',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','69'])).

thf('98',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_D = sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('102',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_D )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('103',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
      | ( sk_D = sk_C_1 ) )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','69','70'])).

thf('106',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ( sk_D = sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_D = sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['99','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    sk_D = sk_C_1 ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['72','109'])).

thf('111',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 != X4 )
      | ~ ( r2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('112',plain,(
    ! [X4: $i] :
      ~ ( r2_xboole_0 @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    $false ),
    inference('sup-',[status(thm)],['110','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HosLCXpFns
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 135 iterations in 0.053s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.50  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(t84_orders_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.50                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.50                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r2_xboole_0 @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.20/0.50        | ~ (r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)) | 
% 0.20/0.50       ~ ((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.20/0.50         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m2_orders_2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.50         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.50           ( ( v6_orders_2 @ C @ A ) & 
% 0.20/0.50             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (l1_orders_2 @ X16)
% 0.20/0.50          | ~ (v5_orders_2 @ X16)
% 0.20/0.50          | ~ (v4_orders_2 @ X16)
% 0.20/0.50          | ~ (v3_orders_2 @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16)
% 0.20/0.50          | ~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X16)))
% 0.20/0.50          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.50          | ~ (m2_orders_2 @ X18 @ X16 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.20/0.50  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '15'])).
% 0.20/0.50  thf(t67_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.50          | (r1_tarski @ X21 @ X19)
% 0.20/0.50          | ~ (m1_orders_2 @ X21 @ X20 @ X19)
% 0.20/0.50          | ~ (l1_orders_2 @ X20)
% 0.20/0.50          | ~ (v5_orders_2 @ X20)
% 0.20/0.50          | ~ (v4_orders_2 @ X20)
% 0.20/0.50          | ~ (v3_orders_2 @ X20)
% 0.20/0.50          | (v2_struct_0 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.50          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.50          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.20/0.50  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.20/0.50      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((r1_tarski @ sk_C_1 @ sk_D))
% 0.20/0.50         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '25'])).
% 0.20/0.50  thf(d8_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X3 : $i, X5 : $i]:
% 0.20/0.50         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((((sk_C_1) = (sk_D)) | (r2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.20/0.50         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (r2_xboole_0 @ sk_C_1 @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((((sk_C_1) = (sk_D)))
% 0.20/0.50         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.20/0.50             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.20/0.50         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))
% 0.20/0.50         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.20/0.50             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf(t69_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.50          | ((X22) = (k1_xboole_0))
% 0.20/0.50          | ~ (m1_orders_2 @ X24 @ X23 @ X22)
% 0.20/0.50          | ~ (m1_orders_2 @ X22 @ X23 @ X24)
% 0.20/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.50          | ~ (l1_orders_2 @ X23)
% 0.20/0.50          | ~ (v5_orders_2 @ X23)
% 0.20/0.50          | ~ (v4_orders_2 @ X23)
% 0.20/0.50          | ~ (v3_orders_2 @ X23)
% 0.20/0.50          | (v2_struct_0 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.20/0.50          | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.20/0.50          | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.50        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 0.20/0.50        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 0.20/0.50        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((((sk_C_1) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((((sk_C_1) = (k1_xboole_0)))
% 0.20/0.50         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.20/0.50             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '47'])).
% 0.20/0.50  thf(t3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t82_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.50         (~ (m1_orders_1 @ X25 @ (k1_orders_1 @ (u1_struct_0 @ X26)))
% 0.20/0.50          | ~ (m2_orders_2 @ X27 @ X26 @ X25)
% 0.20/0.50          | ~ (r1_xboole_0 @ X28 @ X27)
% 0.20/0.50          | ~ (m2_orders_2 @ X28 @ X26 @ X25)
% 0.20/0.50          | ~ (l1_orders_2 @ X26)
% 0.20/0.50          | ~ (v5_orders_2 @ X26)
% 0.20/0.50          | ~ (v4_orders_2 @ X26)
% 0.20/0.50          | ~ (v3_orders_2 @ X26)
% 0.20/0.50          | (v2_struct_0 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | ~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '61'])).
% 0.20/0.50  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain, (~ (r1_xboole_0 @ sk_C_1 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '64'])).
% 0.20/0.50  thf('66', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.20/0.50         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.20/0.50             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '66'])).
% 0.20/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.50  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((r2_xboole_0 @ sk_C_1 @ sk_D)) | 
% 0.20/0.50       ~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (((r2_xboole_0 @ sk_C_1 @ sk_D)) | ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('71', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['3', '69', '70'])).
% 0.20/0.50  thf('72', plain, ((r2_xboole_0 @ sk_C_1 @ sk_D)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '71'])).
% 0.20/0.50  thf('73', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t83_orders_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.50                   ( ( ( C ) != ( D ) ) =>
% 0.20/0.50                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.20/0.50                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.50         (~ (m1_orders_1 @ X29 @ (k1_orders_1 @ (u1_struct_0 @ X30)))
% 0.20/0.50          | ~ (m2_orders_2 @ X31 @ X30 @ X29)
% 0.20/0.50          | (m1_orders_2 @ X31 @ X30 @ X32)
% 0.20/0.50          | (m1_orders_2 @ X32 @ X30 @ X31)
% 0.20/0.50          | ((X32) = (X31))
% 0.20/0.50          | ~ (m2_orders_2 @ X32 @ X30 @ X29)
% 0.20/0.50          | ~ (l1_orders_2 @ X30)
% 0.20/0.50          | ~ (v5_orders_2 @ X30)
% 0.20/0.50          | ~ (v4_orders_2 @ X30)
% 0.20/0.50          | ~ (v3_orders_2 @ X30)
% 0.20/0.50          | (v2_struct_0 @ X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | ((X0) = (X1))
% 0.20/0.50          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.50          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.50          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('79', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('80', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('81', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | ((X0) = (X1))
% 0.20/0.50          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.50          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.50          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.50          | (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.50          | (m1_orders_2 @ sk_D @ sk_A @ X0)
% 0.20/0.50          | ((sk_D) = (X0))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '82'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((sk_D) = (sk_C_1))
% 0.20/0.50        | (m1_orders_2 @ sk_D @ sk_A @ sk_C_1)
% 0.20/0.50        | (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.50          | (r1_tarski @ X21 @ X19)
% 0.20/0.50          | ~ (m1_orders_2 @ X21 @ X20 @ X19)
% 0.20/0.50          | ~ (l1_orders_2 @ X20)
% 0.20/0.50          | ~ (v5_orders_2 @ X20)
% 0.20/0.50          | ~ (v4_orders_2 @ X20)
% 0.20/0.50          | ~ (v3_orders_2 @ X20)
% 0.20/0.50          | (v2_struct_0 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.20/0.50          | (r1_tarski @ X0 @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.50  thf('88', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('89', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('90', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.20/0.50          | (r1_tarski @ X0 @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.20/0.50  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ sk_C_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.20/0.50        | ((sk_D) = (sk_C_1))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (r1_tarski @ sk_D @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['84', '94'])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.20/0.50         <= (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('97', plain, (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['3', '69'])).
% 0.20/0.50  thf('98', plain, (~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      (((r1_tarski @ sk_D @ sk_C_1)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | ((sk_D) = (sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['95', '98'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (((r2_xboole_0 @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('101', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X3 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      (((r1_tarski @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('103', plain,
% 0.20/0.50      (![X10 : $i, X12 : $i]:
% 0.20/0.50         (((X10) = (X12))
% 0.20/0.50          | ~ (r1_tarski @ X12 @ X10)
% 0.20/0.50          | ~ (r1_tarski @ X10 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      (((~ (r1_tarski @ sk_D @ sk_C_1) | ((sk_D) = (sk_C_1))))
% 0.20/0.50         <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.50  thf('105', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['3', '69', '70'])).
% 0.20/0.50  thf('106', plain, ((~ (r1_tarski @ sk_D @ sk_C_1) | ((sk_D) = (sk_C_1)))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['104', '105'])).
% 0.20/0.50  thf('107', plain, ((((sk_D) = (sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['99', '106'])).
% 0.20/0.50  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('109', plain, (((sk_D) = (sk_C_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['107', '108'])).
% 0.20/0.50  thf('110', plain, ((r2_xboole_0 @ sk_C_1 @ sk_C_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['72', '109'])).
% 0.20/0.50  thf('111', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]: (((X3) != (X4)) | ~ (r2_xboole_0 @ X3 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.50  thf('112', plain, (![X4 : $i]: ~ (r2_xboole_0 @ X4 @ X4)),
% 0.20/0.50      inference('simplify', [status(thm)], ['111'])).
% 0.20/0.50  thf('113', plain, ($false), inference('sup-', [status(thm)], ['110', '112'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
