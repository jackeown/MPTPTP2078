%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EAKE78m5rz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  222 ( 330 expanded)
%              Number of equality atoms :   31 (  53 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ ( k2_tarski @ X35 @ X38 ) )
      | ( X37
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X35: $i,X38: $i] :
      ( r1_tarski @ ( k1_tarski @ X35 ) @ ( k2_tarski @ X35 @ X38 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k1_tarski @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('6',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_A )
      | ( X39 = sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X37
        = ( k2_tarski @ X35 @ X36 ) )
      | ( X37
        = ( k1_tarski @ X36 ) )
      | ( X37
        = ( k1_tarski @ X35 ) )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EAKE78m5rz
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 126 iterations in 0.057s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('0', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf(l45_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.22/0.52       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.22/0.52            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X35 : $i, X37 : $i, X38 : $i]:
% 0.22/0.52         ((r1_tarski @ X37 @ (k2_tarski @ X35 @ X38))
% 0.22/0.52          | ((X37) != (k1_tarski @ X35)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X35 : $i, X38 : $i]:
% 0.22/0.52         (r1_tarski @ (k1_tarski @ X35) @ (k2_tarski @ X35 @ X38))),
% 0.22/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.52  thf(l1_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X32 : $i, X33 : $i]:
% 0.22/0.52         ((r2_hidden @ X32 @ X33) | ~ (r1_tarski @ (k1_tarski @ X32) @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(d3_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf(t41_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X39 : $i]: (~ (r2_hidden @ X39 @ sk_A) | ((X39) = (sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X1 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ sk_B @ X0)
% 0.22/0.52          | (r1_tarski @ sk_A @ X0)
% 0.22/0.52          | (r1_tarski @ sk_A @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.52  thf('11', plain, (![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.52         (((X37) = (k2_tarski @ X35 @ X36))
% 0.22/0.52          | ((X37) = (k1_tarski @ X36))
% 0.22/0.52          | ((X37) = (k1_tarski @ X35))
% 0.22/0.52          | ((X37) = (k1_xboole_0))
% 0.22/0.52          | ~ (r1_tarski @ X37 @ (k2_tarski @ X35 @ X36)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ((sk_A) = (k1_tarski @ sk_B))
% 0.22/0.52          | ((sk_A) = (k1_tarski @ X0))
% 0.22/0.52          | ((sk_A) = (k2_tarski @ sk_B @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((sk_A) = (k1_tarski @ X0)) | ((sk_A) = (k2_tarski @ sk_B @ X0)))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['13', '14', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((((sk_A) = (k1_tarski @ sk_B)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['0', '16'])).
% 0.22/0.52  thf('18', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.22/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.52  thf('19', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
