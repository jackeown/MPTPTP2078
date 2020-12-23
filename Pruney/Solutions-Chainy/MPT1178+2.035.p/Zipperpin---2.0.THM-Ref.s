%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lLuPuBWZlT

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 196 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  620 (2296 expanded)
%              Number of equality atoms :   26 ( 107 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('1',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ( ( k3_tarski @ X20 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( m1_orders_1 @ X5 @ ( k1_orders_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k4_orders_2 @ X6 @ X5 ) )
      | ( m2_orders_2 @ X9 @ X6 @ X5 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k4_orders_2 @ X6 @ X5 ) )
      | ( m2_orders_2 @ X9 @ X6 @ X5 )
      | ~ ( m1_orders_1 @ X5 @ ( k1_orders_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ~ ( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(clc,[status(thm)],['20','30'])).

thf('32',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(clc,[status(thm)],['20','30'])).

thf('33',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_orders_1 @ X15 @ ( k1_orders_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m2_orders_2 @ X17 @ X16 @ X15 )
      | ~ ( r1_xboole_0 @ X18 @ X17 )
      | ~ ( m2_orders_2 @ X18 @ X16 @ X15 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('43',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r2_hidden @ X19 @ X20 )
      | ( ( k3_tarski @ X20 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['31','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lLuPuBWZlT
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:35:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 156 iterations in 0.052s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.51  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.51  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.51  thf(d1_xboole_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.51  thf(t87_orders_2, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t91_orders_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.51            ( ![B:$i]:
% 0.22/0.51              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.22/0.51       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.51            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i]:
% 0.22/0.51         (((X19) = (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X19 @ X20)
% 0.22/0.51          | ((k3_tarski @ X20) != (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.51          | ((X0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((X0) = (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.51        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.51        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.51        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.51        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d17_orders_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_orders_1 @ X5 @ (k1_orders_1 @ (u1_struct_0 @ X6)))
% 0.22/0.51          | ((X7) != (k4_orders_2 @ X6 @ X5))
% 0.22/0.51          | (m2_orders_2 @ X9 @ X6 @ X5)
% 0.22/0.51          | ~ (r2_hidden @ X9 @ X7)
% 0.22/0.51          | ~ (l1_orders_2 @ X6)
% 0.22/0.51          | ~ (v5_orders_2 @ X6)
% 0.22/0.51          | ~ (v4_orders_2 @ X6)
% 0.22/0.51          | ~ (v3_orders_2 @ X6)
% 0.22/0.51          | (v2_struct_0 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X6)
% 0.22/0.52          | ~ (v3_orders_2 @ X6)
% 0.22/0.52          | ~ (v4_orders_2 @ X6)
% 0.22/0.52          | ~ (v5_orders_2 @ X6)
% 0.22/0.52          | ~ (l1_orders_2 @ X6)
% 0.22/0.52          | ~ (r2_hidden @ X9 @ (k4_orders_2 @ X6 @ X5))
% 0.22/0.52          | (m2_orders_2 @ X9 @ X6 @ X5)
% 0.22/0.52          | ~ (m1_orders_1 @ X5 @ (k1_orders_1 @ (u1_struct_0 @ X6))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '11'])).
% 0.22/0.52  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.22/0.52  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.52          | (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.22/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.52        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(fc9_orders_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.22/0.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X13)
% 0.22/0.52          | ~ (v5_orders_2 @ X13)
% 0.22/0.52          | ~ (v4_orders_2 @ X13)
% 0.22/0.52          | ~ (v3_orders_2 @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13)
% 0.22/0.52          | ~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.22/0.52          | ~ (v1_xboole_0 @ (k4_orders_2 @ X13 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.22/0.52  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.22/0.52      inference('clc', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 0.22/0.52      inference('clc', [status(thm)], ['20', '30'])).
% 0.22/0.52  thf('32', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 0.22/0.52      inference('clc', [status(thm)], ['20', '30'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t82_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         (~ (m1_orders_1 @ X15 @ (k1_orders_1 @ (u1_struct_0 @ X16)))
% 0.22/0.52          | ~ (m2_orders_2 @ X17 @ X16 @ X15)
% 0.22/0.52          | ~ (r1_xboole_0 @ X18 @ X17)
% 0.22/0.52          | ~ (m2_orders_2 @ X18 @ X16 @ X15)
% 0.22/0.52          | ~ (l1_orders_2 @ X16)
% 0.22/0.52          | ~ (v5_orders_2 @ X16)
% 0.22/0.52          | ~ (v4_orders_2 @ X16)
% 0.22/0.52          | ~ (v3_orders_2 @ X16)
% 0.22/0.52          | (v2_struct_0 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.22/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_2))),
% 0.22/0.52      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.22/0.52          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '40'])).
% 0.22/0.52  thf(t98_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.22/0.52       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k3_tarski @ X3) @ X4)
% 0.22/0.52          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.22/0.52  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.52  thf('43', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i]:
% 0.22/0.52         (((X19) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X19 @ X20)
% 0.22/0.52          | ((k3_tarski @ X20) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.52          | ((X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k3_tarski @ k1_xboole_0) @ X0)
% 0.22/0.52          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['42', '46'])).
% 0.22/0.52  thf('48', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k3_tarski @ X3) @ X4)
% 0.22/0.52          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.52          | (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (r1_xboole_0 @ (k3_tarski @ k1_xboole_0) @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['49', '50'])).
% 0.22/0.52  thf('52', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.52          | (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.52  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.52  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.52      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['41', '58'])).
% 0.22/0.52  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('61', plain, (![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)),
% 0.22/0.52      inference('clc', [status(thm)], ['59', '60'])).
% 0.22/0.52  thf('62', plain, ($false), inference('sup-', [status(thm)], ['31', '61'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
