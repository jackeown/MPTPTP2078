%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.me16dsS6Qn

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  82 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  296 ( 640 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
      | ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ( r2_hidden @ X16 @ X17 )
      | ( X17
       != ( k2_tarski @ X18 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('15',plain,(
    ! [X15: $i,X18: $i] :
      ( r2_hidden @ X15 @ ( k2_tarski @ X18 @ X15 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('24',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['11','22','23'])).

thf('25',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['10','24'])).

thf('26',plain,
    ( $false
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['11','22'])).

thf('28',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.me16dsS6Qn
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:01:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 58 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(t65_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.48       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.48          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.48        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(l27_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X24 : $i, X25 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X24) @ X25) | (r2_hidden @ X24 @ X25))),
% 0.21/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(t83_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ X1)
% 0.21/0.48          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_A)
% 0.21/0.48        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.21/0.48         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.21/0.48         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_A))
% 0.21/0.48         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.21/0.48       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['7'])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(d2_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.48         (((X16) != (X15))
% 0.21/0.48          | (r2_hidden @ X16 @ X17)
% 0.21/0.48          | ((X17) != (k2_tarski @ X18 @ X15)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X15 : $i, X18 : $i]: (r2_hidden @ X15 @ (k2_tarski @ X18 @ X15))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['13', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(d5_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.48          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.48          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.48          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.21/0.48         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.21/0.48       ((r2_hidden @ sk_B @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['7'])).
% 0.21/0.48  thf('24', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['11', '22', '23'])).
% 0.21/0.48  thf('25', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['10', '24'])).
% 0.21/0.48  thf('26', plain, (($false) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['1', '25'])).
% 0.21/0.48  thf('27', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['11', '22'])).
% 0.21/0.48  thf('28', plain, ($false),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['26', '27'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
