%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOX0S82vec

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 722 expanded)
%              Number of leaves         :   38 ( 221 expanded)
%              Depth                    :   23
%              Number of atoms          : 1135 (12571 expanded)
%              Number of equality atoms :   29 (  59 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_orders_1 @ X19 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m2_orders_2 @ X20 @ X18 @ X19 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_orders_2 @ X23 @ X22 @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_orders_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m2_orders_2 @ X29 @ X28 @ X27 )
      | ~ ( r1_xboole_0 @ X30 @ X29 )
      | ~ ( m2_orders_2 @ X30 @ X28 @ X27 )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( r1_xboole_0 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','69'])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','70'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','73','74'])).

thf('76',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','75'])).

thf('77',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
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

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_orders_1 @ X31 @ ( k1_orders_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m2_orders_2 @ X33 @ X32 @ X31 )
      | ( m1_orders_2 @ X33 @ X32 @ X34 )
      | ( m1_orders_2 @ X34 @ X32 @ X33 )
      | ( X34 = X33 )
      | ~ ( m2_orders_2 @ X34 @ X32 @ X31 )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('81',plain,(
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
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( m1_orders_2 @ sk_C_1 @ sk_A @ X0 )
      | ( sk_C_1 = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('90',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_orders_2 @ X23 @ X22 @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','98'])).

thf('100',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','73'])).

thf('102',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('106',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_D )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
      | ( sk_D = sk_C_1 ) )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','73','74'])).

thf('110',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ( sk_D = sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_C_1 = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    sk_C_1 = sk_D ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['76','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('116',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    $false ),
    inference('sup-',[status(thm)],['114','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOX0S82vec
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 158 iterations in 0.063s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.52  thf(t84_orders_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.52                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.52                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((r2_xboole_0 @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.21/0.52        | ~ (r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)) | 
% 0.21/0.52       ~ ((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.21/0.52         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('5', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m2_orders_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.52           ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.52             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X18)
% 0.21/0.52          | ~ (v5_orders_2 @ X18)
% 0.21/0.52          | ~ (v4_orders_2 @ X18)
% 0.21/0.52          | ~ (v3_orders_2 @ X18)
% 0.21/0.52          | (v2_struct_0 @ X18)
% 0.21/0.52          | ~ (m1_orders_1 @ X19 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.21/0.52          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.52          | ~ (m2_orders_2 @ X20 @ X18 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.21/0.52  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '15'])).
% 0.21/0.52  thf(t67_orders_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.52          | (r1_tarski @ X23 @ X21)
% 0.21/0.52          | ~ (m1_orders_2 @ X23 @ X22 @ X21)
% 0.21/0.52          | ~ (l1_orders_2 @ X22)
% 0.21/0.52          | ~ (v5_orders_2 @ X22)
% 0.21/0.52          | ~ (v4_orders_2 @ X22)
% 0.21/0.52          | ~ (v3_orders_2 @ X22)
% 0.21/0.52          | (v2_struct_0 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.21/0.52          | (r1_tarski @ X0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.21/0.52          | (r1_tarski @ X0 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.21/0.52  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.21/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (((r1_tarski @ sk_C_1 @ sk_D))
% 0.21/0.52         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '25'])).
% 0.21/0.52  thf(d8_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.52       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (((((sk_C_1) = (sk_D)) | (r2_xboole_0 @ sk_C_1 @ sk_D)))
% 0.21/0.52         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((~ (r2_xboole_0 @ sk_C_1 @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((((sk_C_1) = (sk_D)))
% 0.21/0.52         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.21/0.52             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.21/0.52         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))
% 0.21/0.52         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.21/0.52             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf(t69_orders_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.52          | ((X24) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_orders_2 @ X26 @ X25 @ X24)
% 0.21/0.52          | ~ (m1_orders_2 @ X24 @ X25 @ X26)
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.52          | ~ (l1_orders_2 @ X25)
% 0.21/0.52          | ~ (v5_orders_2 @ X25)
% 0.21/0.52          | ~ (v4_orders_2 @ X25)
% 0.21/0.52          | ~ (v3_orders_2 @ X25)
% 0.21/0.52          | (v2_struct_0 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.21/0.52          | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.21/0.52          | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.52        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 0.21/0.52        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 0.21/0.52        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.52  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((((sk_C_1) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((((sk_C_1) = (k1_xboole_0)))
% 0.21/0.52         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.21/0.52             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '47'])).
% 0.21/0.52  thf(t3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.52  thf(dt_k2_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.52  thf('51', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('52', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.21/0.52      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf(t5_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.52          | ~ (v1_xboole_0 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '54'])).
% 0.21/0.52  thf('56', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('57', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t82_orders_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X28)))
% 0.21/0.52          | ~ (m2_orders_2 @ X29 @ X28 @ X27)
% 0.21/0.52          | ~ (r1_xboole_0 @ X30 @ X29)
% 0.21/0.52          | ~ (m2_orders_2 @ X30 @ X28 @ X27)
% 0.21/0.52          | ~ (l1_orders_2 @ X28)
% 0.21/0.52          | ~ (v5_orders_2 @ X28)
% 0.21/0.52          | ~ (v4_orders_2 @ X28)
% 0.21/0.52          | ~ (v3_orders_2 @ X28)
% 0.21/0.52          | (v2_struct_0 @ X28))),
% 0.21/0.52      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.52          | ~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '65'])).
% 0.21/0.52  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('69', plain, (~ (r1_xboole_0 @ sk_C_1 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '68'])).
% 0.21/0.52  thf('70', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.21/0.52         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D)) & 
% 0.21/0.52             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '70'])).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (((r2_xboole_0 @ sk_C_1 @ sk_D)) | 
% 0.21/0.52       ~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (((r2_xboole_0 @ sk_C_1 @ sk_D)) | ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('75', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['3', '73', '74'])).
% 0.21/0.52  thf('76', plain, ((r2_xboole_0 @ sk_C_1 @ sk_D)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['1', '75'])).
% 0.21/0.52  thf('77', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('78', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t83_orders_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.21/0.52                   ( ( ( C ) != ( D ) ) =>
% 0.21/0.52                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.21/0.52                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X31 @ (k1_orders_1 @ (u1_struct_0 @ X32)))
% 0.21/0.52          | ~ (m2_orders_2 @ X33 @ X32 @ X31)
% 0.21/0.53          | (m1_orders_2 @ X33 @ X32 @ X34)
% 0.21/0.53          | (m1_orders_2 @ X34 @ X32 @ X33)
% 0.21/0.53          | ((X34) = (X33))
% 0.21/0.53          | ~ (m2_orders_2 @ X34 @ X32 @ X31)
% 0.21/0.53          | ~ (l1_orders_2 @ X32)
% 0.21/0.53          | ~ (v5_orders_2 @ X32)
% 0.21/0.53          | ~ (v4_orders_2 @ X32)
% 0.21/0.53          | ~ (v3_orders_2 @ X32)
% 0.21/0.53          | (v2_struct_0 @ X32))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.53          | ((X0) = (X1))
% 0.21/0.53          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.53          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.53          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.53  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.53          | ((X0) = (X1))
% 0.21/0.53          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.21/0.53          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.21/0.53          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.53          | (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.21/0.53          | (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.53          | ((sk_C_1) = (X0))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['78', '86'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((sk_C_1) = (sk_D))
% 0.21/0.53        | (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.21/0.53        | (m1_orders_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['77', '87'])).
% 0.21/0.53  thf('89', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.53          | (r1_tarski @ X23 @ X21)
% 0.21/0.53          | ~ (m1_orders_2 @ X23 @ X22 @ X21)
% 0.21/0.53          | ~ (l1_orders_2 @ X22)
% 0.21/0.53          | ~ (v5_orders_2 @ X22)
% 0.21/0.53          | ~ (v4_orders_2 @ X22)
% 0.21/0.53          | ~ (v3_orders_2 @ X22)
% 0.21/0.53          | (v2_struct_0 @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.21/0.53          | (r1_tarski @ X0 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.53  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 0.21/0.53          | (r1_tarski @ X0 @ sk_C_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.21/0.53  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ X0 @ sk_C_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.53  thf('99', plain,
% 0.21/0.53      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)
% 0.21/0.53        | ((sk_C_1) = (sk_D))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (r1_tarski @ sk_D @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['88', '98'])).
% 0.21/0.53  thf('100', plain,
% 0.21/0.53      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))
% 0.21/0.53         <= (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('101', plain, (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['3', '73'])).
% 0.21/0.53  thf('102', plain, (~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['100', '101'])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      (((r1_tarski @ sk_D @ sk_C_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | ((sk_C_1) = (sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['99', '102'])).
% 0.21/0.53  thf('104', plain,
% 0.21/0.53      (((r2_xboole_0 @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('105', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.53  thf('106', plain,
% 0.21/0.53      (((r1_tarski @ sk_C_1 @ sk_D)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('107', plain,
% 0.21/0.53      (![X7 : $i, X9 : $i]:
% 0.21/0.53         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('108', plain,
% 0.21/0.53      (((~ (r1_tarski @ sk_D @ sk_C_1) | ((sk_D) = (sk_C_1))))
% 0.21/0.53         <= (((r2_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.53  thf('109', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['3', '73', '74'])).
% 0.21/0.53  thf('110', plain, ((~ (r1_tarski @ sk_D @ sk_C_1) | ((sk_D) = (sk_C_1)))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['108', '109'])).
% 0.21/0.53  thf('111', plain, ((((sk_C_1) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['103', '110'])).
% 0.21/0.53  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('113', plain, (((sk_C_1) = (sk_D))),
% 0.21/0.53      inference('clc', [status(thm)], ['111', '112'])).
% 0.21/0.53  thf('114', plain, ((r2_xboole_0 @ sk_C_1 @ sk_C_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['76', '113'])).
% 0.21/0.53  thf('115', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.53  thf('116', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['115'])).
% 0.21/0.53  thf('117', plain, ($false), inference('sup-', [status(thm)], ['114', '116'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
