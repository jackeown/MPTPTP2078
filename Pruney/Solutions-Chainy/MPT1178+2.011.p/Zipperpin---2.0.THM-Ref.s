%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2lChjMRffj

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 168 expanded)
%              Number of leaves         :   32 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  540 (1960 expanded)
%              Number of equality atoms :   12 (  72 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ? [C: $i] :
          ( m2_orders_2 @ C @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_orders_1 @ X21 @ ( k1_orders_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m2_orders_2 @ ( sk_C_1 @ X21 @ X20 ) @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('2',plain,
    ( ( m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ sk_A_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A_1 )
    | ~ ( v3_orders_2 @ sk_A_1 )
    | ~ ( v4_orders_2 @ sk_A_1 )
    | ~ ( v5_orders_2 @ sk_A_1 )
    | ~ ( l1_orders_2 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ sk_A_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ sk_A_1 @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ sk_A_1 @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('14',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A_1 ) ) ),
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

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m2_orders_2 @ X24 @ X23 @ X22 )
      | ~ ( r1_xboole_0 @ X25 @ X24 )
      | ~ ( m2_orders_2 @ X25 @ X23 @ X22 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v3_orders_2 @ sk_A_1 )
      | ~ ( v4_orders_2 @ sk_A_1 )
      | ~ ( v5_orders_2 @ sk_A_1 )
      | ~ ( l1_orders_2 @ sk_A_1 )
      | ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ X0 )
      | ( v2_struct_0 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ sk_A_1 @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('28',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A_1 ) ) ),
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

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( X16
       != ( k4_orders_2 @ X15 @ X14 ) )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( m2_orders_2 @ X17 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m2_orders_2 @ X17 @ X15 @ X14 )
      | ( r2_hidden @ X17 @ ( k4_orders_2 @ X15 @ X14 ) )
      | ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A_1 @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A_1 )
      | ~ ( v5_orders_2 @ sk_A_1 )
      | ~ ( v4_orders_2 @ sk_A_1 )
      | ~ ( v3_orders_2 @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v5_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A_1 @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A_1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ ( k4_orders_2 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('41',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_A_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','46'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('48',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('49',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['26','47','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2lChjMRffj
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 45 iterations in 0.025s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.49  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.22/0.49  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.22/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.49  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.22/0.49  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.22/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(t87_orders_2, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(existence_m2_orders_2, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.22/0.49         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X20 : $i, X21 : $i]:
% 0.22/0.49         (~ (l1_orders_2 @ X20)
% 0.22/0.49          | ~ (v5_orders_2 @ X20)
% 0.22/0.49          | ~ (v4_orders_2 @ X20)
% 0.22/0.49          | ~ (v3_orders_2 @ X20)
% 0.22/0.49          | (v2_struct_0 @ X20)
% 0.22/0.49          | ~ (m1_orders_1 @ X21 @ (k1_orders_1 @ (u1_struct_0 @ X20)))
% 0.22/0.49          | (m2_orders_2 @ (sk_C_1 @ X21 @ X20) @ X20 @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ sk_A_1 @ sk_B_1)
% 0.22/0.49        | (v2_struct_0 @ sk_A_1)
% 0.22/0.49        | ~ (v3_orders_2 @ sk_A_1)
% 0.22/0.49        | ~ (v4_orders_2 @ sk_A_1)
% 0.22/0.49        | ~ (v5_orders_2 @ sk_A_1)
% 0.22/0.49        | ~ (l1_orders_2 @ sk_A_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((v3_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain, ((v4_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('5', plain, ((v5_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, ((l1_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ sk_A_1 @ sk_B_1)
% 0.22/0.49        | (v2_struct_0 @ sk_A_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.22/0.49  thf('8', plain, (~ (v2_struct_0 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ sk_A_1 @ sk_B_1)),
% 0.22/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf(t3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.49  thf(d1_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ sk_A_1 @ sk_B_1)),
% 0.22/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t82_orders_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.22/0.49               ( ![D:$i]:
% 0.22/0.49                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.49         (~ (m1_orders_1 @ X22 @ (k1_orders_1 @ (u1_struct_0 @ X23)))
% 0.22/0.49          | ~ (m2_orders_2 @ X24 @ X23 @ X22)
% 0.22/0.49          | ~ (r1_xboole_0 @ X25 @ X24)
% 0.22/0.49          | ~ (m2_orders_2 @ X25 @ X23 @ X22)
% 0.22/0.49          | ~ (l1_orders_2 @ X23)
% 0.22/0.49          | ~ (v5_orders_2 @ X23)
% 0.22/0.49          | ~ (v4_orders_2 @ X23)
% 0.22/0.49          | ~ (v3_orders_2 @ X23)
% 0.22/0.49          | (v2_struct_0 @ X23))),
% 0.22/0.49      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A_1)
% 0.22/0.49          | ~ (v3_orders_2 @ sk_A_1)
% 0.22/0.49          | ~ (v4_orders_2 @ sk_A_1)
% 0.22/0.49          | ~ (v5_orders_2 @ sk_A_1)
% 0.22/0.49          | ~ (l1_orders_2 @ sk_A_1)
% 0.22/0.49          | ~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1)
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.49          | ~ (m2_orders_2 @ X1 @ sk_A_1 @ sk_B_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, ((v3_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain, ((v4_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('19', plain, ((v5_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('20', plain, ((l1_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A_1)
% 0.22/0.49          | ~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1)
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.49          | ~ (m2_orders_2 @ X1 @ sk_A_1 @ sk_B_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1)
% 0.22/0.49          | ~ (r1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ X0)
% 0.22/0.49          | (v2_struct_0 @ sk_A_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '21'])).
% 0.22/0.49  thf('23', plain, (~ (v2_struct_0 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ X0)
% 0.22/0.49          | ~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ X0) | ~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '24'])).
% 0.22/0.49  thf('26', plain, (~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ sk_A_1 @ sk_B_1)),
% 0.22/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d17_orders_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.22/0.49               ( ![D:$i]:
% 0.22/0.49                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.49         (~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.22/0.49          | ((X16) != (k4_orders_2 @ X15 @ X14))
% 0.22/0.49          | (r2_hidden @ X17 @ X16)
% 0.22/0.49          | ~ (m2_orders_2 @ X17 @ X15 @ X14)
% 0.22/0.49          | ~ (l1_orders_2 @ X15)
% 0.22/0.49          | ~ (v5_orders_2 @ X15)
% 0.22/0.49          | ~ (v4_orders_2 @ X15)
% 0.22/0.49          | ~ (v3_orders_2 @ X15)
% 0.22/0.49          | (v2_struct_0 @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.22/0.49         ((v2_struct_0 @ X15)
% 0.22/0.49          | ~ (v3_orders_2 @ X15)
% 0.22/0.49          | ~ (v4_orders_2 @ X15)
% 0.22/0.49          | ~ (v5_orders_2 @ X15)
% 0.22/0.49          | ~ (l1_orders_2 @ X15)
% 0.22/0.49          | ~ (m2_orders_2 @ X17 @ X15 @ X14)
% 0.22/0.49          | (r2_hidden @ X17 @ (k4_orders_2 @ X15 @ X14))
% 0.22/0.49          | ~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X15))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A_1 @ sk_B_1))
% 0.22/0.49          | ~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1)
% 0.22/0.49          | ~ (l1_orders_2 @ sk_A_1)
% 0.22/0.49          | ~ (v5_orders_2 @ sk_A_1)
% 0.22/0.49          | ~ (v4_orders_2 @ sk_A_1)
% 0.22/0.49          | ~ (v3_orders_2 @ sk_A_1)
% 0.22/0.49          | (v2_struct_0 @ sk_A_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['28', '30'])).
% 0.22/0.49  thf('32', plain, ((l1_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('33', plain, ((v5_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('34', plain, ((v4_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain, ((v3_orders_2 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A_1 @ sk_B_1))
% 0.22/0.49          | ~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1)
% 0.22/0.49          | (v2_struct_0 @ sk_A_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.22/0.49  thf('37', plain, (~ (v2_struct_0 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m2_orders_2 @ X0 @ sk_A_1 @ sk_B_1)
% 0.22/0.49          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A_1 @ sk_B_1)))),
% 0.22/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ 
% 0.22/0.49        (k4_orders_2 @ sk_A_1 @ sk_B_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '38'])).
% 0.22/0.49  thf(l49_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         ((r1_tarski @ X12 @ (k3_tarski @ X13)) | ~ (r2_hidden @ X12 @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      ((r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ 
% 0.22/0.49        (k3_tarski @ (k4_orders_2 @ sk_A_1 @ sk_B_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (((k3_tarski @ (k4_orders_2 @ sk_A_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('43', plain, ((r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A_1) @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.49  thf('44', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X8 : $i, X10 : $i]:
% 0.22/0.49         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf('47', plain, (((sk_C_1 @ sk_B_1 @ sk_A_1) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.49  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.22/0.49  thf('48', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.22/0.49  thf('49', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.22/0.49  thf(l13_xboole_0, axiom,
% 0.22/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.49  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.49  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['48', '51'])).
% 0.22/0.49  thf('53', plain, ($false),
% 0.22/0.49      inference('demod', [status(thm)], ['26', '47', '52'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
