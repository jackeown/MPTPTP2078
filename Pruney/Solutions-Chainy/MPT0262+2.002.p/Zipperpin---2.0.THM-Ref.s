%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y19K2z6w6W

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:30 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  249 ( 411 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t57_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ B )
          & ~ ( r2_hidden @ C @ B )
          & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t57_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y19K2z6w6W
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.72/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.93  % Solved by: fo/fo7.sh
% 0.72/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.93  % done 742 iterations in 0.480s
% 0.72/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.93  % SZS output start Refutation
% 0.72/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.93  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.72/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.93  thf(t57_zfmisc_1, conjecture,
% 0.72/0.93    (![A:$i,B:$i,C:$i]:
% 0.72/0.93     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.72/0.93          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.72/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.93        ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.72/0.93             ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ) )),
% 0.72/0.93    inference('cnf.neg', [status(esa)], [t57_zfmisc_1])).
% 0.72/0.93  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.72/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.93  thf(t3_xboole_0, axiom,
% 0.72/0.93    (![A:$i,B:$i]:
% 0.72/0.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.72/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.72/0.93  thf('1', plain,
% 0.72/0.93      (![X2 : $i, X3 : $i]:
% 0.72/0.93         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.72/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.93  thf(d1_tarski, axiom,
% 0.72/0.93    (![A:$i,B:$i]:
% 0.72/0.93     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.72/0.93       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.72/0.93  thf('2', plain,
% 0.72/0.93      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.72/0.93         (~ (r2_hidden @ X13 @ X12)
% 0.72/0.93          | ((X13) = (X10))
% 0.72/0.93          | ((X12) != (k1_tarski @ X10)))),
% 0.72/0.93      inference('cnf', [status(esa)], [d1_tarski])).
% 0.72/0.93  thf('3', plain,
% 0.72/0.93      (![X10 : $i, X13 : $i]:
% 0.72/0.93         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.72/0.93      inference('simplify', [status(thm)], ['2'])).
% 0.72/0.93  thf('4', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.72/0.93          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['1', '3'])).
% 0.72/0.93  thf('5', plain,
% 0.72/0.93      (![X2 : $i, X3 : $i]:
% 0.72/0.93         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.72/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.93  thf('6', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r2_hidden @ X0 @ X1)
% 0.72/0.93          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.72/0.93          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.72/0.93      inference('sup+', [status(thm)], ['4', '5'])).
% 0.72/0.93  thf('7', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.72/0.93      inference('simplify', [status(thm)], ['6'])).
% 0.72/0.93  thf('8', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.72/0.93      inference('simplify', [status(thm)], ['6'])).
% 0.72/0.93  thf(t70_xboole_1, axiom,
% 0.72/0.93    (![A:$i,B:$i,C:$i]:
% 0.72/0.93     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.72/0.93            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.72/0.93       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.72/0.93            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.72/0.93  thf('9', plain,
% 0.72/0.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.72/0.93         ((r1_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.72/0.93          | ~ (r1_xboole_0 @ X6 @ X7)
% 0.72/0.93          | ~ (r1_xboole_0 @ X6 @ X8))),
% 0.72/0.93      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.72/0.93  thf('10', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         ((r2_hidden @ X0 @ X1)
% 0.72/0.93          | ~ (r1_xboole_0 @ X1 @ X2)
% 0.72/0.93          | (r1_xboole_0 @ X1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.72/0.93  thf('11', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         ((r2_hidden @ X0 @ X1)
% 0.72/0.93          | (r1_xboole_0 @ X1 @ 
% 0.72/0.93             (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_tarski @ X0)))
% 0.78/0.93          | (r2_hidden @ X2 @ X1))),
% 0.78/0.93      inference('sup-', [status(thm)], ['7', '10'])).
% 0.78/0.93  thf(t41_enumset1, axiom,
% 0.78/0.93    (![A:$i,B:$i]:
% 0.78/0.93     ( ( k2_tarski @ A @ B ) =
% 0.78/0.93       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.78/0.93  thf('12', plain,
% 0.78/0.93      (![X15 : $i, X16 : $i]:
% 0.78/0.93         ((k2_tarski @ X15 @ X16)
% 0.78/0.93           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.78/0.93      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.78/0.93  thf('13', plain,
% 0.78/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.93         ((r2_hidden @ X0 @ X1)
% 0.78/0.93          | (r1_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))
% 0.78/0.93          | (r2_hidden @ X2 @ X1))),
% 0.78/0.93      inference('demod', [status(thm)], ['11', '12'])).
% 0.78/0.93  thf(symmetry_r1_xboole_0, axiom,
% 0.78/0.93    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.78/0.93  thf('14', plain,
% 0.78/0.93      (![X0 : $i, X1 : $i]:
% 0.78/0.93         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.78/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.78/0.93  thf('15', plain,
% 0.78/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.93         ((r2_hidden @ X1 @ X2)
% 0.78/0.93          | (r2_hidden @ X0 @ X2)
% 0.78/0.93          | (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.78/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.78/0.93  thf('16', plain, (~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B)),
% 0.78/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.93  thf('17', plain, (((r2_hidden @ sk_C_2 @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.78/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.78/0.93  thf('18', plain, (~ (r2_hidden @ sk_C_2 @ sk_B)),
% 0.78/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.93  thf('19', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.78/0.93      inference('clc', [status(thm)], ['17', '18'])).
% 0.78/0.93  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.78/0.93  
% 0.78/0.93  % SZS output end Refutation
% 0.78/0.93  
% 0.78/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
