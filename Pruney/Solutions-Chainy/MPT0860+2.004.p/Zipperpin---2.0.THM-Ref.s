%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CVsfILXpvo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 775 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t16_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ( X12
        = ( k4_xboole_0 @ X12 @ ( k2_tarski @ X11 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 )
       != ( k2_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X2 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_D @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('24',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['16','24'])).

thf('26',plain,(
    r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('28',plain,
    ( sk_C_1
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['20'])).

thf('30',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('31',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['22','30'])).

thf('32',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CVsfILXpvo
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 79 iterations in 0.042s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(t16_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.49         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.20/0.49          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.49            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t16_mcart_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t10_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.20/0.49          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t144_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.20/0.49          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         ((r2_hidden @ X11 @ X12)
% 0.20/0.49          | (r2_hidden @ X13 @ X12)
% 0.20/0.49          | ((X12) = (k4_xboole_0 @ X12 @ (k2_tarski @ X11 @ X13))))),
% 0.20/0.49      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('4', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t72_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.49       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X14 @ X15)
% 0.20/0.49          | ((k4_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15)
% 0.20/0.49              != (k2_tarski @ X14 @ X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k2_tarski @ X0 @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k2_tarski @ X2 @ X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_tarski @ X2 @ X1))
% 0.20/0.49          | (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.20/0.49        | (r2_hidden @ sk_C_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.49  thf(d1_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i]:
% 0.20/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r2_hidden @ sk_C_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.20/0.49        | ((sk_D) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.49        | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.20/0.49          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.49  thf('19', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.20/0.49        | ((k2_mcart_1 @ sk_A) != (sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.20/0.49         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['20'])).
% 0.20/0.49  thf('22', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | 
% 0.20/0.49       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.49      inference('split', [status(esa)], ['15'])).
% 0.20/0.49  thf('24', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['16', '24'])).
% 0.20/0.49  thf('26', plain, ((r2_hidden @ sk_C_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['14', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i]:
% 0.20/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('28', plain, (((sk_C_1) = (k2_mcart_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((k2_mcart_1 @ sk_A) != (sk_C_1)))
% 0.20/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['20'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.20/0.49       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.20/0.49      inference('split', [status(esa)], ['20'])).
% 0.20/0.49  thf('31', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['22', '30'])).
% 0.20/0.49  thf('32', plain, (((k2_mcart_1 @ sk_A) != (sk_C_1))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.20/0.49  thf('33', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['28', '32'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
