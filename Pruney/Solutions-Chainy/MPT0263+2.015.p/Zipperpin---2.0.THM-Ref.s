%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iKLQQAWsdr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  274 ( 370 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
        = ( k1_tarski @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iKLQQAWsdr
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:32:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 115 iterations in 0.042s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(t4_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X8 @ X9)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.47  thf(t48_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.47           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.47  thf(d5_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.47       ( ![D:$i]:
% 0.20/0.47         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.47           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.47          | (r2_hidden @ X6 @ X3)
% 0.20/0.47          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.47         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.47  thf(d1_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.47          | ((X17) = (X14))
% 0.20/0.47          | ((X16) != (k1_tarski @ X14)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X14 : $i, X17 : $i]:
% 0.20/0.47         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.20/0.47          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X8 @ X9)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.20/0.47          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.47  thf(t58_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.47       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.47          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.20/0.47  thf('16', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf(l31_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.47       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X26 @ (k1_tarski @ X25)) = (k1_tarski @ X25))
% 0.20/0.47          | ~ (r2_hidden @ X25 @ X26))),
% 0.20/0.47      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['19', '22'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
