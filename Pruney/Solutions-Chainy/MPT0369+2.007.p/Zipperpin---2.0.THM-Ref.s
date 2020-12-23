%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1ONVyZ8Bu9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  77 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  371 ( 551 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_xboole_0 @ X22 @ X20 )
      | ( r1_tarski @ X22 @ ( k3_subset_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X19: $i] :
      ( X19
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X6 ) )
      | ( r2_hidden @ X3 @ X6 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['25','30'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1ONVyZ8Bu9
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:39:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 116 iterations in 0.026s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(t50_subset_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.47               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.47                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.47                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.47                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 0.21/0.47  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t4_subset_1, axiom,
% 0.21/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X23 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.47  thf(t43_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.47             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.21/0.47          | ~ (r1_xboole_0 @ X22 @ X20)
% 0.21/0.47          | (r1_tarski @ X22 @ (k3_subset_1 @ X21 @ X20))
% 0.21/0.47          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.21/0.47          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.21/0.47          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('4', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.47  thf(t22_subset_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X19 : $i]:
% 0.21/0.47         ((k2_subset_1 @ X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.47  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.47  thf('6', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X19 : $i]: ((X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['4', '7'])).
% 0.21/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.47  thf('9', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.21/0.47  thf('11', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '10'])).
% 0.21/0.47  thf(t28_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.47  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.47  thf(t100_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.47           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.47  thf('16', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d2_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X12 @ X13)
% 0.21/0.47          | (r2_hidden @ X12 @ X13)
% 0.21/0.47          | (v1_xboole_0 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.47  thf('18', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf(t1_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.47       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.47         ((r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X6))
% 0.21/0.47          | (r2_hidden @ X3 @ X6)
% 0.21/0.47          | ~ (r2_hidden @ X3 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ sk_A)
% 0.21/0.47          | (r2_hidden @ sk_C @ X0)
% 0.21/0.47          | (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.21/0.47          | (r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.21/0.47          | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['15', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ sk_C @ (k3_xboole_0 @ X0 @ sk_A))
% 0.21/0.47          | (v1_xboole_0 @ sk_A)
% 0.21/0.47          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['14', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (((r2_hidden @ sk_C @ sk_B)
% 0.21/0.47        | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.21/0.47        | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '22'])).
% 0.21/0.47  thf('24', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain, (~ (r2_hidden @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d5_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.21/0.47          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, (~ (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['26', '29'])).
% 0.21/0.47  thf('31', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('clc', [status(thm)], ['25', '30'])).
% 0.21/0.47  thf(l13_xboole_0, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('35', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
