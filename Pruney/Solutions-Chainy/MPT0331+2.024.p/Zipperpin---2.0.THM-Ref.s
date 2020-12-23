%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fk71wTazNz

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:06 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :  293 ( 435 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X6 @ X8 ) @ X9 )
        = ( k2_tarski @ X6 @ X8 ) )
      | ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fk71wTazNz
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:41:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.58/1.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.58/1.76  % Solved by: fo/fo7.sh
% 1.58/1.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.58/1.76  % done 1266 iterations in 1.287s
% 1.58/1.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.58/1.76  % SZS output start Refutation
% 1.58/1.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.58/1.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.58/1.76  thf(sk_A_type, type, sk_A: $i).
% 1.58/1.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.58/1.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.58/1.76  thf(sk_C_type, type, sk_C: $i).
% 1.58/1.76  thf(sk_B_type, type, sk_B: $i).
% 1.58/1.76  thf(t144_zfmisc_1, conjecture,
% 1.58/1.76    (![A:$i,B:$i,C:$i]:
% 1.58/1.76     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.58/1.76          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 1.58/1.76  thf(zf_stmt_0, negated_conjecture,
% 1.58/1.76    (~( ![A:$i,B:$i,C:$i]:
% 1.58/1.76        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 1.58/1.76             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 1.58/1.76    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 1.58/1.76  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 1.58/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.76  thf(t72_zfmisc_1, axiom,
% 1.58/1.76    (![A:$i,B:$i,C:$i]:
% 1.58/1.76     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.58/1.76       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 1.58/1.76  thf('1', plain,
% 1.58/1.76      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.58/1.76         (((k4_xboole_0 @ (k2_tarski @ X6 @ X8) @ X9) = (k2_tarski @ X6 @ X8))
% 1.58/1.76          | (r2_hidden @ X8 @ X9)
% 1.58/1.76          | (r2_hidden @ X6 @ X9))),
% 1.58/1.76      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 1.58/1.76  thf(d5_xboole_0, axiom,
% 1.58/1.76    (![A:$i,B:$i,C:$i]:
% 1.58/1.76     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.58/1.76       ( ![D:$i]:
% 1.58/1.76         ( ( r2_hidden @ D @ C ) <=>
% 1.58/1.76           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.58/1.76  thf('2', plain,
% 1.58/1.76      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.58/1.76         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.58/1.76          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.58/1.76          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.58/1.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.58/1.76  thf('3', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.58/1.76          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.58/1.76      inference('eq_fact', [status(thm)], ['2'])).
% 1.58/1.76  thf('4', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.58/1.76          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.58/1.76      inference('eq_fact', [status(thm)], ['2'])).
% 1.58/1.76  thf('5', plain,
% 1.58/1.76      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.58/1.76         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.58/1.76          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.58/1.76          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.58/1.76          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.58/1.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.58/1.76  thf('6', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.58/1.76          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.58/1.76          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.58/1.76          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.58/1.76      inference('sup-', [status(thm)], ['4', '5'])).
% 1.58/1.76  thf('7', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.58/1.76          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.58/1.76          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.58/1.76      inference('simplify', [status(thm)], ['6'])).
% 1.58/1.76  thf('8', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.58/1.76          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.58/1.76      inference('eq_fact', [status(thm)], ['2'])).
% 1.58/1.76  thf('9', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.58/1.76          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.58/1.76      inference('clc', [status(thm)], ['7', '8'])).
% 1.58/1.76  thf('10', plain,
% 1.58/1.76      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.58/1.76         (~ (r2_hidden @ X4 @ X3)
% 1.58/1.76          | ~ (r2_hidden @ X4 @ X2)
% 1.58/1.76          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.58/1.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.58/1.76  thf('11', plain,
% 1.58/1.76      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.58/1.76         (~ (r2_hidden @ X4 @ X2)
% 1.58/1.76          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.58/1.76      inference('simplify', [status(thm)], ['10'])).
% 1.58/1.76  thf('12', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.76         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.58/1.76          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.58/1.76      inference('sup-', [status(thm)], ['9', '11'])).
% 1.58/1.76  thf('13', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.58/1.76          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.58/1.76      inference('sup-', [status(thm)], ['3', '12'])).
% 1.58/1.76  thf('14', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i]:
% 1.58/1.76         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.58/1.76      inference('simplify', [status(thm)], ['13'])).
% 1.58/1.76  thf('15', plain,
% 1.58/1.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.76         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 1.58/1.76          | (r2_hidden @ X1 @ X2)
% 1.58/1.76          | (r2_hidden @ X0 @ X2))),
% 1.58/1.76      inference('sup+', [status(thm)], ['1', '14'])).
% 1.58/1.76  thf('16', plain,
% 1.58/1.76      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.58/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.76  thf('17', plain,
% 1.58/1.76      ((((sk_C) != (sk_C))
% 1.58/1.76        | (r2_hidden @ sk_B @ sk_C)
% 1.58/1.76        | (r2_hidden @ sk_A @ sk_C))),
% 1.58/1.76      inference('sup-', [status(thm)], ['15', '16'])).
% 1.58/1.76  thf('18', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 1.58/1.76      inference('simplify', [status(thm)], ['17'])).
% 1.58/1.76  thf('19', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 1.58/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.76  thf('20', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.58/1.76      inference('clc', [status(thm)], ['18', '19'])).
% 1.58/1.76  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 1.58/1.76  
% 1.58/1.76  % SZS output end Refutation
% 1.58/1.76  
% 1.58/1.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
