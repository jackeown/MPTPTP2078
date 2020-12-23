%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3wPd19lq7G

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:26 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 135 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  602 (1380 expanded)
%              Number of equality atoms :   28 (  65 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

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
    m1_orders_1 @ sk_B_4 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_orders_2 @ X37 )
      | ~ ( v5_orders_2 @ X37 )
      | ~ ( v4_orders_2 @ X37 )
      | ~ ( v3_orders_2 @ X37 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_orders_1 @ X38 @ ( k1_orders_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_4 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_4 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_4 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ ( k1_zfmisc_1 @ ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ ( k4_orders_2 @ sk_A @ sk_B_4 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('17',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_4 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( k4_orders_2 @ sk_A @ sk_B_4 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    m1_orders_1 @ sk_B_4 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('24',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ~ ( m1_orders_1 @ X30 @ ( k1_orders_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X32
       != ( k4_orders_2 @ X31 @ X30 ) )
      | ( m2_orders_2 @ X34 @ X31 @ X30 )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('25',plain,(
    ! [X30: $i,X31: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( r2_hidden @ X34 @ ( k4_orders_2 @ X31 @ X30 ) )
      | ( m2_orders_2 @ X34 @ X31 @ X30 )
      | ~ ( m1_orders_1 @ X30 @ ( k1_orders_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_4 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_4 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_4 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_4 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_4 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k4_orders_2 @ sk_A @ sk_B_4 )
        = k1_xboole_0 )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,
    ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_4 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_4 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','34'])).

thf('36',plain,(
    m1_orders_1 @ sk_B_4 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('37',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_orders_1 @ X39 @ ( k1_orders_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X39 @ ( u1_struct_0 @ X40 ) ) @ X41 )
      | ~ ( m2_orders_2 @ X41 @ X40 @ X39 )
      | ~ ( l1_orders_2 @ X40 )
      | ~ ( v5_orders_2 @ X40 )
      | ~ ( v4_orders_2 @ X40 )
      | ~ ( v3_orders_2 @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_4 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
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
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_4 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_4 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','45'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('47',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(s1_xboole_0__e5_6__mcart_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
    ! [C: $i] :
      ( ( r2_hidden @ C @ B )
    <=> ( ( r2_hidden @ C @ ( k3_tarski @ ( k3_tarski @ ( k3_tarski @ ( k3_tarski @ ( k3_tarski @ A ) ) ) ) ) )
        & ~ ( r1_xboole_0 @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ ( sk_B_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e5_6__mcart_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ ( sk_B_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e5_6__mcart_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_orders_2 @ sk_A @ sk_B_4 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['46','55'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['9','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3wPd19lq7G
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 857 iterations in 0.503s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i > $i).
% 0.77/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.96  thf(sk_B_4_type, type, sk_B_4: $i).
% 0.77/0.96  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.77/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.77/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.96  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.77/0.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.77/0.96  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.77/0.96  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.77/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.96  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.77/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.96  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.77/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.77/0.96  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.77/0.96  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.77/0.96  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.77/0.96  thf(t87_orders_2, conjecture,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.96         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i]:
% 0.77/0.96        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.96            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.77/0.96          ( ![B:$i]:
% 0.77/0.96            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      ((m1_orders_1 @ sk_B_4 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(fc9_orders_2, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.96         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.77/0.96         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.96       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      (![X37 : $i, X38 : $i]:
% 0.77/0.96         (~ (l1_orders_2 @ X37)
% 0.77/0.96          | ~ (v5_orders_2 @ X37)
% 0.77/0.96          | ~ (v4_orders_2 @ X37)
% 0.77/0.96          | ~ (v3_orders_2 @ X37)
% 0.77/0.96          | (v2_struct_0 @ X37)
% 0.77/0.96          | ~ (m1_orders_1 @ X38 @ (k1_orders_1 @ (u1_struct_0 @ X37)))
% 0.77/0.96          | ~ (v1_xboole_0 @ (k4_orders_2 @ X37 @ X38)))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_4))
% 0.77/0.96        | (v2_struct_0 @ sk_A)
% 0.77/0.96        | ~ (v3_orders_2 @ sk_A)
% 0.77/0.96        | ~ (v4_orders_2 @ sk_A)
% 0.77/0.96        | ~ (v5_orders_2 @ sk_A)
% 0.77/0.96        | ~ (l1_orders_2 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['0', '1'])).
% 0.77/0.96  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_4)) | (v2_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.77/0.96  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('9', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_4))),
% 0.77/0.96      inference('clc', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.77/0.96  thf('10', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.77/0.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.77/0.96  thf(d1_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.77/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X5 @ X6)
% 0.77/0.96          | (r2_hidden @ X5 @ X7)
% 0.77/0.96          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]:
% 0.77/0.96         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.77/0.96      inference('simplify', [status(thm)], ['11'])).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['10', '12'])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_4)) = (k1_xboole_0))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t100_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      (![X15 : $i]: (r1_tarski @ X15 @ (k1_zfmisc_1 @ (k3_tarski @ X15)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      ((r1_tarski @ (k4_orders_2 @ sk_A @ sk_B_4) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['14', '15'])).
% 0.77/0.96  thf(t1_zfmisc_1, axiom,
% 0.77/0.96    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.77/0.96  thf('17', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.77/0.96      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.77/0.96  thf(l3_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.77/0.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.77/0.96  thf('18', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i]:
% 0.77/0.96         (((X11) = (k1_tarski @ X10))
% 0.77/0.96          | ((X11) = (k1_xboole_0))
% 0.77/0.96          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 0.77/0.96      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.77/0.96          | ((X0) = (k1_xboole_0))
% 0.77/0.96          | ((X0) = (k1_tarski @ k1_xboole_0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['17', '18'])).
% 0.77/0.96  thf('20', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.77/0.96      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.77/0.96          | ((X0) = (k1_xboole_0))
% 0.77/0.96          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      ((((k4_orders_2 @ sk_A @ sk_B_4) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.77/0.96        | ((k4_orders_2 @ sk_A @ sk_B_4) = (k1_xboole_0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['16', '21'])).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      ((m1_orders_1 @ sk_B_4 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(d17_orders_2, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.96         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.77/0.96               ( ![D:$i]:
% 0.77/0.96                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.77/0.96         (~ (m1_orders_1 @ X30 @ (k1_orders_1 @ (u1_struct_0 @ X31)))
% 0.77/0.96          | ((X32) != (k4_orders_2 @ X31 @ X30))
% 0.77/0.96          | (m2_orders_2 @ X34 @ X31 @ X30)
% 0.77/0.96          | ~ (r2_hidden @ X34 @ X32)
% 0.77/0.96          | ~ (l1_orders_2 @ X31)
% 0.77/0.96          | ~ (v5_orders_2 @ X31)
% 0.77/0.96          | ~ (v4_orders_2 @ X31)
% 0.77/0.96          | ~ (v3_orders_2 @ X31)
% 0.77/0.96          | (v2_struct_0 @ X31))),
% 0.77/0.96      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      (![X30 : $i, X31 : $i, X34 : $i]:
% 0.77/0.96         ((v2_struct_0 @ X31)
% 0.77/0.96          | ~ (v3_orders_2 @ X31)
% 0.77/0.96          | ~ (v4_orders_2 @ X31)
% 0.77/0.96          | ~ (v5_orders_2 @ X31)
% 0.77/0.96          | ~ (l1_orders_2 @ X31)
% 0.77/0.96          | ~ (r2_hidden @ X34 @ (k4_orders_2 @ X31 @ X30))
% 0.77/0.96          | (m2_orders_2 @ X34 @ X31 @ X30)
% 0.77/0.96          | ~ (m1_orders_1 @ X30 @ (k1_orders_1 @ (u1_struct_0 @ X31))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['24'])).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((m2_orders_2 @ X0 @ sk_A @ sk_B_4)
% 0.77/0.96          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_4))
% 0.77/0.96          | ~ (l1_orders_2 @ sk_A)
% 0.77/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.77/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.77/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.77/0.96          | (v2_struct_0 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['23', '25'])).
% 0.77/0.96  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('28', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('29', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((m2_orders_2 @ X0 @ sk_A @ sk_B_4)
% 0.77/0.96          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_4))
% 0.77/0.96          | (v2_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.77/0.96  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_4))
% 0.77/0.96          | (m2_orders_2 @ X0 @ sk_A @ sk_B_4))),
% 0.77/0.96      inference('clc', [status(thm)], ['31', '32'])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.77/0.96          | ((k4_orders_2 @ sk_A @ sk_B_4) = (k1_xboole_0))
% 0.77/0.96          | (m2_orders_2 @ X0 @ sk_A @ sk_B_4))),
% 0.77/0.96      inference('sup-', [status(thm)], ['22', '33'])).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_4)
% 0.77/0.96        | ((k4_orders_2 @ sk_A @ sk_B_4) = (k1_xboole_0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['13', '34'])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      ((m1_orders_1 @ sk_B_4 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t79_orders_2, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.96         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.77/0.96               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.77/0.96         (~ (m1_orders_1 @ X39 @ (k1_orders_1 @ (u1_struct_0 @ X40)))
% 0.77/0.96          | (r2_hidden @ (k1_funct_1 @ X39 @ (u1_struct_0 @ X40)) @ X41)
% 0.77/0.96          | ~ (m2_orders_2 @ X41 @ X40 @ X39)
% 0.77/0.96          | ~ (l1_orders_2 @ X40)
% 0.77/0.96          | ~ (v5_orders_2 @ X40)
% 0.77/0.96          | ~ (v4_orders_2 @ X40)
% 0.77/0.96          | ~ (v3_orders_2 @ X40)
% 0.77/0.96          | (v2_struct_0 @ X40))),
% 0.77/0.96      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v2_struct_0 @ sk_A)
% 0.77/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.77/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.77/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.77/0.96          | ~ (l1_orders_2 @ sk_A)
% 0.77/0.96          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_4)
% 0.77/0.96          | (r2_hidden @ (k1_funct_1 @ sk_B_4 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/0.96  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('43', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((v2_struct_0 @ sk_A)
% 0.77/0.96          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_4)
% 0.77/0.96          | (r2_hidden @ (k1_funct_1 @ sk_B_4 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.77/0.96  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('45', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((r2_hidden @ (k1_funct_1 @ sk_B_4 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.77/0.96          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_4))),
% 0.77/0.96      inference('clc', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      ((((k4_orders_2 @ sk_A @ sk_B_4) = (k1_xboole_0))
% 0.77/0.96        | (r2_hidden @ (k1_funct_1 @ sk_B_4 @ (u1_struct_0 @ sk_A)) @ 
% 0.77/0.96           k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['35', '45'])).
% 0.77/0.96  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.77/0.96  thf('47', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.77/0.96      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.77/0.96  thf(t7_xboole_0, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/0.96          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.77/0.96      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/0.96  thf(s1_xboole_0__e5_6__mcart_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ?[B:$i]:
% 0.77/0.96       ( ![C:$i]:
% 0.77/0.96         ( ( r2_hidden @ C @ B ) <=>
% 0.77/0.96           ( ( r2_hidden @
% 0.77/0.96               C @ 
% 0.77/0.96               ( k3_tarski @
% 0.77/0.96                 ( k3_tarski @
% 0.77/0.96                   ( k3_tarski @ ( k3_tarski @ ( k3_tarski @ A ) ) ) ) ) ) & 
% 0.77/0.96             ( ~( r1_xboole_0 @ C @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i]:
% 0.77/0.96         (~ (r1_xboole_0 @ X18 @ X19) | ~ (r2_hidden @ X18 @ (sk_B_1 @ X19)))),
% 0.77/0.96      inference('cnf', [status(esa)], [s1_xboole_0__e5_6__mcart_1])).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((sk_B_1 @ X0) = (k1_xboole_0))
% 0.77/0.96          | ~ (r1_xboole_0 @ (sk_B @ (sk_B_1 @ X0)) @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.96  thf('51', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['47', '50'])).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i]:
% 0.77/0.96         (~ (r1_xboole_0 @ X18 @ X19) | ~ (r2_hidden @ X18 @ (sk_B_1 @ X19)))),
% 0.77/0.96      inference('cnf', [status(esa)], [s1_xboole_0__e5_6__mcart_1])).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/0.96  thf('54', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.77/0.96      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.77/0.96  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.77/0.96      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.96  thf('56', plain, (((k4_orders_2 @ sk_A @ sk_B_4) = (k1_xboole_0))),
% 0.77/0.96      inference('clc', [status(thm)], ['46', '55'])).
% 0.77/0.96  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.77/0.96  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.96  thf('58', plain, ($false),
% 0.77/0.96      inference('demod', [status(thm)], ['9', '56', '57'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
