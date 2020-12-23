%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F2Qx4ldrQv

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 115 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  539 (1312 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
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
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('11',plain,
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

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r2_hidden @ X17 @ X18 )
      | ( ( k3_tarski @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('17',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k4_orders_2 @ X7 @ X6 ) )
      | ( m2_orders_2 @ X10 @ X7 @ X6 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_orders_2 @ X7 @ X6 ) )
      | ( m2_orders_2 @ X10 @ X7 @ X6 )
      | ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ ( u1_struct_0 @ X15 ) ) @ X16 )
      | ~ ( m2_orders_2 @ X16 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,
    ( ( k4_orders_2 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['9','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F2Qx4ldrQv
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 46 iterations in 0.024s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.44  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.44  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.44  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.44  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.44  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.44  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.21/0.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.44  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.44  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.44  thf(t87_orders_2, conjecture,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.44           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i]:
% 0.21/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.44            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.44          ( ![B:$i]:
% 0.21/0.44            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.44              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(fc9_orders_2, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.44         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.44       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      (![X12 : $i, X13 : $i]:
% 0.21/0.44         (~ (l1_orders_2 @ X12)
% 0.21/0.44          | ~ (v5_orders_2 @ X12)
% 0.21/0.44          | ~ (v4_orders_2 @ X12)
% 0.21/0.44          | ~ (v3_orders_2 @ X12)
% 0.21/0.44          | (v2_struct_0 @ X12)
% 0.21/0.44          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.21/0.44          | ~ (v1_xboole_0 @ (k4_orders_2 @ X12 @ X13)))),
% 0.21/0.44      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.44        | (v2_struct_0 @ sk_A)
% 0.21/0.44        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.44        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.44        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.44        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.44  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.21/0.44      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.44  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('9', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.21/0.44      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.44  thf(t9_mcart_1, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.44          ( ![B:$i]:
% 0.21/0.44            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.44                 ( ![C:$i,D:$i]:
% 0.21/0.44                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.44                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.21/0.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(t91_orders_1, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.44            ( ![B:$i]:
% 0.21/0.44              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.21/0.44       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.44            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X17 : $i, X18 : $i]:
% 0.21/0.44         (((X17) = (k1_xboole_0))
% 0.21/0.44          | ~ (r2_hidden @ X17 @ X18)
% 0.21/0.44          | ((k3_tarski @ X18) != (k1_xboole_0)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.44          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.44          | ((X0) = (k1_xboole_0)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.44  thf('14', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (((X0) = (k1_xboole_0))
% 0.21/0.44          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.21/0.44      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.44  thf('15', plain,
% 0.21/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.44        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['10', '14'])).
% 0.21/0.44  thf('16', plain,
% 0.21/0.44      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.21/0.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.44  thf('17', plain,
% 0.21/0.44      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.44        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.44        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.21/0.44      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.44  thf('18', plain,
% 0.21/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.44        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.21/0.44      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.44  thf('19', plain,
% 0.21/0.44      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(d17_orders_2, axiom,
% 0.21/0.44    (![A:$i]:
% 0.21/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.44       ( ![B:$i]:
% 0.21/0.44         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.44           ( ![C:$i]:
% 0.21/0.44             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.21/0.44               ( ![D:$i]:
% 0.21/0.44                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.44  thf('20', plain,
% 0.21/0.44      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.44         (~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7)))
% 0.21/0.44          | ((X8) != (k4_orders_2 @ X7 @ X6))
% 0.21/0.44          | (m2_orders_2 @ X10 @ X7 @ X6)
% 0.21/0.44          | ~ (r2_hidden @ X10 @ X8)
% 0.21/0.44          | ~ (l1_orders_2 @ X7)
% 0.21/0.44          | ~ (v5_orders_2 @ X7)
% 0.21/0.44          | ~ (v4_orders_2 @ X7)
% 0.21/0.44          | ~ (v3_orders_2 @ X7)
% 0.21/0.44          | (v2_struct_0 @ X7))),
% 0.21/0.44      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.44  thf('21', plain,
% 0.21/0.44      (![X6 : $i, X7 : $i, X10 : $i]:
% 0.21/0.44         ((v2_struct_0 @ X7)
% 0.21/0.44          | ~ (v3_orders_2 @ X7)
% 0.21/0.44          | ~ (v4_orders_2 @ X7)
% 0.21/0.44          | ~ (v5_orders_2 @ X7)
% 0.21/0.44          | ~ (l1_orders_2 @ X7)
% 0.21/0.44          | ~ (r2_hidden @ X10 @ (k4_orders_2 @ X7 @ X6))
% 0.21/0.44          | (m2_orders_2 @ X10 @ X7 @ X6)
% 0.21/0.44          | ~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7))))),
% 0.21/0.44      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.44  thf('22', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.44          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.44          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.44          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.44          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.44          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.44          | (v2_struct_0 @ sk_A))),
% 0.21/0.44      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.44  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('26', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('27', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.45          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.45          | (v2_struct_0 @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.21/0.45  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('29', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.45          | (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.21/0.45      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.45  thf('30', plain,
% 0.21/0.45      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.45        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.21/0.45      inference('sup-', [status(thm)], ['18', '29'])).
% 0.21/0.45  thf('31', plain,
% 0.21/0.45      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(t79_orders_2, axiom,
% 0.21/0.45    (![A:$i]:
% 0.21/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.45       ( ![B:$i]:
% 0.21/0.45         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.45           ( ![C:$i]:
% 0.21/0.45             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.45               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.21/0.45  thf('32', plain,
% 0.21/0.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.45         (~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.21/0.45          | (r2_hidden @ (k1_funct_1 @ X14 @ (u1_struct_0 @ X15)) @ X16)
% 0.21/0.45          | ~ (m2_orders_2 @ X16 @ X15 @ X14)
% 0.21/0.45          | ~ (l1_orders_2 @ X15)
% 0.21/0.45          | ~ (v5_orders_2 @ X15)
% 0.21/0.45          | ~ (v4_orders_2 @ X15)
% 0.21/0.45          | ~ (v3_orders_2 @ X15)
% 0.21/0.45          | (v2_struct_0 @ X15))),
% 0.21/0.45      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.21/0.45  thf('33', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((v2_struct_0 @ sk_A)
% 0.21/0.45          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.45          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.45          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.45          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.45          | (r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.45  thf('34', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('35', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('36', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('38', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((v2_struct_0 @ sk_A)
% 0.21/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.45          | (r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.21/0.45  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('40', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.21/0.45          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.21/0.45      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.45  thf('41', plain,
% 0.21/0.45      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.45        | (r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.45           k1_xboole_0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['30', '40'])).
% 0.21/0.45  thf(t7_ordinal1, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.45  thf('42', plain,
% 0.21/0.45      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.45  thf('43', plain,
% 0.21/0.45      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.45        | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.21/0.45             (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.45      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.45  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.45  thf('45', plain, (((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.45  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.45  thf('47', plain, ($false),
% 0.21/0.45      inference('demod', [status(thm)], ['9', '45', '46'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
