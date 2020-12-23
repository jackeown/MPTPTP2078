%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DX8lv7Iiwy

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  176 (1493 expanded)
%              Number of leaves         :   36 ( 450 expanded)
%              Depth                    :   30
%              Number of atoms          : 1416 (21734 expanded)
%              Number of equality atoms :   38 ( 882 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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

thf('0',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ X0 ) @ ( sk_B @ X0 ) )
      | ( ( k3_tarski @ X0 )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0
      = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X15
       != ( k4_orders_2 @ X14 @ X13 ) )
      | ( m2_orders_2 @ X17 @ X14 @ X13 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k4_orders_2 @ X14 @ X13 ) )
      | ( m2_orders_2 @ X17 @ X14 @ X13 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X18: $i] :
      ( ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X13 @ X14 ) @ X18 )
      | ( m2_orders_2 @ ( sk_D_1 @ X18 @ X13 @ X14 ) @ X14 @ X13 )
      | ( X18
        = ( k4_orders_2 @ X14 @ X13 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X15
       != ( k4_orders_2 @ X14 @ X13 ) )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( m2_orders_2 @ X16 @ X14 @ X13 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( m2_orders_2 @ X16 @ X14 @ X13 )
      | ( r2_hidden @ X16 @ ( k4_orders_2 @ X14 @ X13 ) )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( ( sk_D_1 @ X0 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_orders_1 @ X23 @ ( k1_orders_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( ( sk_D_1 @ X0 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v6_orders_2 @ X21 @ X19 )
      | ~ ( m2_orders_2 @ X21 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
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
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v6_orders_2 @ ( sk_D_1 @ X0 @ sk_B_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('95',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m2_orders_2 @ X21 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['94','104'])).

thf(d16_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v6_orders_2 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( m2_orders_2 @ C @ A @ B )
              <=> ( ( C != k1_xboole_0 )
                  & ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ( ( k1_funct_1 @ B @ ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) )
                          = D ) ) ) ) ) ) ) ) )).

thf('106',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_orders_1 @ X9 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m2_orders_2 @ X11 @ X10 @ X9 )
      | ( X11 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v6_orders_2 @ X11 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('107',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X10 @ X9 )
      | ~ ( m1_orders_1 @ X9 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(condensation,[status(thm)],['119'])).

thf('121',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['25','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('123',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X10 @ X9 )
      | ~ ( m1_orders_1 @ X9 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['25','120'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('128',plain,(
    v6_orders_2 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','128','129','130','131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','135'])).

thf('137',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['25','120'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DX8lv7Iiwy
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 19:04:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 79 iterations in 0.057s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.21/0.52  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.52  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.52  thf(t87_orders_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d1_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf(l49_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         ((r1_tarski @ X7 @ (k3_tarski @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X0) | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i]:
% 0.21/0.52         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (r1_tarski @ (k3_tarski @ X0) @ (sk_B @ X0))
% 0.21/0.52          | ((k3_tarski @ X0) = (sk_B @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((~ (r1_tarski @ k1_xboole_0 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.21/0.52        | ((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52            = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.21/0.52        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.52  thf('8', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((((k1_xboole_0) = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.21/0.52        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d17_orders_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.21/0.52          | ((X15) != (k4_orders_2 @ X14 @ X13))
% 0.21/0.52          | (m2_orders_2 @ X17 @ X14 @ X13)
% 0.21/0.52          | ~ (r2_hidden @ X17 @ X15)
% 0.21/0.52          | ~ (l1_orders_2 @ X14)
% 0.21/0.52          | ~ (v5_orders_2 @ X14)
% 0.21/0.52          | ~ (v4_orders_2 @ X14)
% 0.21/0.52          | ~ (v3_orders_2 @ X14)
% 0.21/0.52          | (v2_struct_0 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X14)
% 0.21/0.52          | ~ (v3_orders_2 @ X14)
% 0.21/0.52          | ~ (v4_orders_2 @ X14)
% 0.21/0.52          | ~ (v5_orders_2 @ X14)
% 0.21/0.52          | ~ (l1_orders_2 @ X14)
% 0.21/0.52          | ~ (r2_hidden @ X17 @ (k4_orders_2 @ X14 @ X13))
% 0.21/0.52          | (m2_orders_2 @ X17 @ X14 @ X13)
% 0.21/0.52          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.52  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.21/0.52  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X18 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X18 @ X13 @ X14) @ X18)
% 0.21/0.52          | (m2_orders_2 @ (sk_D_1 @ X18 @ X13 @ X14) @ X14 @ X13)
% 0.21/0.52          | ((X18) = (k4_orders_2 @ X14 @ X13))
% 0.21/0.52          | ~ (l1_orders_2 @ X14)
% 0.21/0.52          | ~ (v5_orders_2 @ X14)
% 0.21/0.52          | ~ (v4_orders_2 @ X14)
% 0.21/0.52          | ~ (v3_orders_2 @ X14)
% 0.21/0.52          | (v2_struct_0 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (m2_orders_2 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (m2_orders_2 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_orders_2 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.21/0.52          | ((X15) != (k4_orders_2 @ X14 @ X13))
% 0.21/0.52          | (r2_hidden @ X16 @ X15)
% 0.21/0.52          | ~ (m2_orders_2 @ X16 @ X14 @ X13)
% 0.21/0.52          | ~ (l1_orders_2 @ X14)
% 0.21/0.52          | ~ (v5_orders_2 @ X14)
% 0.21/0.52          | ~ (v4_orders_2 @ X14)
% 0.21/0.52          | ~ (v3_orders_2 @ X14)
% 0.21/0.52          | (v2_struct_0 @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X14)
% 0.21/0.52          | ~ (v3_orders_2 @ X14)
% 0.21/0.52          | ~ (v4_orders_2 @ X14)
% 0.21/0.52          | ~ (v5_orders_2 @ X14)
% 0.21/0.52          | ~ (l1_orders_2 @ X14)
% 0.21/0.52          | ~ (m2_orders_2 @ X16 @ X14 @ X13)
% 0.21/0.52          | (r2_hidden @ X16 @ (k4_orders_2 @ X14 @ X13))
% 0.21/0.52          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '38'])).
% 0.21/0.52  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.21/0.52  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.52             (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         ((r1_tarski @ X7 @ (k3_tarski @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (r1_tarski @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.52             (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (r1_tarski @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i]:
% 0.21/0.52         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | ((sk_D_1 @ X0 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_orders_2 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(fc9_orders_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X22)
% 0.21/0.52          | ~ (v5_orders_2 @ X22)
% 0.21/0.52          | ~ (v4_orders_2 @ X22)
% 0.21/0.52          | ~ (v3_orders_2 @ X22)
% 0.21/0.52          | (v2_struct_0 @ X22)
% 0.21/0.52          | ~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X22)))
% 0.21/0.52          | ~ (v1_xboole_0 @ (k4_orders_2 @ X22 @ X23)))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.52  thf('62', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('63', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.21/0.52  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.21/0.52  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0) | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | ((sk_D_1 @ X0 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m2_orders_2 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
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
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X19)
% 0.21/0.52          | ~ (v5_orders_2 @ X19)
% 0.21/0.52          | ~ (v4_orders_2 @ X19)
% 0.21/0.52          | ~ (v3_orders_2 @ X19)
% 0.21/0.52          | (v2_struct_0 @ X19)
% 0.21/0.52          | ~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X19)))
% 0.21/0.52          | (v6_orders_2 @ X21 @ X19)
% 0.21/0.52          | ~ (m2_orders_2 @ X21 @ X19 @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('80', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('81', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.21/0.52  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v6_orders_2 @ (sk_D_1 @ X0 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['75', '85'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['74', '86'])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['87'])).
% 0.21/0.52  thf('89', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['90'])).
% 0.21/0.52  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0) | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('95', plain,
% 0.21/0.52      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X19)
% 0.21/0.52          | ~ (v5_orders_2 @ X19)
% 0.21/0.52          | ~ (v4_orders_2 @ X19)
% 0.21/0.52          | ~ (v3_orders_2 @ X19)
% 0.21/0.52          | (v2_struct_0 @ X19)
% 0.21/0.52          | ~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X19)))
% 0.21/0.52          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.52          | ~ (m2_orders_2 @ X21 @ X19 @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.52  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('99', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('100', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('101', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('102', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.21/0.52  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('104', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.52  thf('105', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['94', '104'])).
% 0.21/0.52  thf(d16_orders_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.52                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.21/0.52                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.21/0.52                   ( ![D:$i]:
% 0.21/0.52                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                       ( ( r2_hidden @ D @ C ) =>
% 0.21/0.52                         ( ( k1_funct_1 @
% 0.21/0.52                             B @ 
% 0.21/0.52                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.21/0.52                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('106', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X9 @ (k1_orders_1 @ (u1_struct_0 @ X10)))
% 0.21/0.52          | ~ (m2_orders_2 @ X11 @ X10 @ X9)
% 0.21/0.52          | ((X11) != (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.52          | ~ (v6_orders_2 @ X11 @ X10)
% 0.21/0.52          | ~ (l1_orders_2 @ X10)
% 0.21/0.52          | ~ (v5_orders_2 @ X10)
% 0.21/0.52          | ~ (v4_orders_2 @ X10)
% 0.21/0.52          | ~ (v3_orders_2 @ X10)
% 0.21/0.52          | (v2_struct_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.21/0.52  thf('107', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X10)
% 0.21/0.52          | ~ (v3_orders_2 @ X10)
% 0.21/0.52          | ~ (v4_orders_2 @ X10)
% 0.21/0.52          | ~ (v5_orders_2 @ X10)
% 0.21/0.52          | ~ (l1_orders_2 @ X10)
% 0.21/0.52          | ~ (v6_orders_2 @ k1_xboole_0 @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ X10 @ X9)
% 0.21/0.52          | ~ (m1_orders_1 @ X9 @ (k1_orders_1 @ (u1_struct_0 @ X10))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['106'])).
% 0.21/0.52  thf('108', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X1)
% 0.21/0.52          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.52          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['105', '107'])).
% 0.21/0.52  thf('109', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('110', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('111', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('112', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('113', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X1)
% 0.21/0.52          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.52          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.21/0.52  thf('114', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X2)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.52          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['93', '113'])).
% 0.21/0.52  thf('115', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '114'])).
% 0.21/0.52  thf('116', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X2)
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['72', '115'])).
% 0.21/0.52  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('118', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['116', '117'])).
% 0.21/0.52  thf('119', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('condensation', [status(thm)], ['118'])).
% 0.21/0.52  thf('120', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.21/0.52      inference('condensation', [status(thm)], ['119'])).
% 0.21/0.52  thf('121', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '120'])).
% 0.21/0.52  thf('122', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.52  thf('123', plain,
% 0.21/0.52      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.52  thf('124', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X10)
% 0.21/0.52          | ~ (v3_orders_2 @ X10)
% 0.21/0.52          | ~ (v4_orders_2 @ X10)
% 0.21/0.52          | ~ (v5_orders_2 @ X10)
% 0.21/0.52          | ~ (l1_orders_2 @ X10)
% 0.21/0.52          | ~ (v6_orders_2 @ k1_xboole_0 @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ X10 @ X9)
% 0.21/0.52          | ~ (m1_orders_1 @ X9 @ (k1_orders_1 @ (u1_struct_0 @ X10))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['106'])).
% 0.21/0.52  thf('125', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.52          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['123', '124'])).
% 0.21/0.52  thf('126', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '120'])).
% 0.21/0.52  thf('127', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf('128', plain, ((v6_orders_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['126', '127'])).
% 0.21/0.52  thf('129', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('130', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('131', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('132', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('133', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['125', '128', '129', '130', '131', '132'])).
% 0.21/0.52  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('135', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.52          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('clc', [status(thm)], ['133', '134'])).
% 0.21/0.52  thf('136', plain, (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '135'])).
% 0.21/0.52  thf('137', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '120'])).
% 0.21/0.52  thf('138', plain, ($false), inference('demod', [status(thm)], ['136', '137'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
