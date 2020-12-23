%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QejOOwGvWP

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:32 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  292 ( 334 expanded)
%              Number of equality atoms :   41 (  47 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X27 @ X26 ) @ X26 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( sk_C_1 @ X27 @ X26 )
       != X27 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QejOOwGvWP
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 269 iterations in 0.222s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.68  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.68  thf(t58_zfmisc_1, conjecture,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.47/0.68       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i]:
% 0.47/0.68        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.47/0.68          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.47/0.68  thf('0', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(l44_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i]:
% 0.47/0.68         (((X26) = (k1_xboole_0))
% 0.47/0.68          | (r2_hidden @ (sk_C_1 @ X27 @ X26) @ X26)
% 0.47/0.68          | ((X26) = (k1_tarski @ X27)))),
% 0.47/0.68      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.68  thf(d4_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.47/0.68       ( ![D:$i]:
% 0.47/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.68           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X6 @ X5)
% 0.47/0.68          | (r2_hidden @ X6 @ X4)
% 0.47/0.68          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.47/0.68         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['2'])).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (((k3_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 0.47/0.68          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.47/0.68          | (r2_hidden @ (sk_C_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['1', '3'])).
% 0.47/0.68  thf(d1_tarski, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X14 @ X13)
% 0.47/0.68          | ((X14) = (X11))
% 0.47/0.68          | ((X13) != (k1_tarski @ X11)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (![X11 : $i, X14 : $i]:
% 0.47/0.68         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.47/0.68          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_tarski @ X2))
% 0.47/0.68          | ((sk_C_1 @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))) = (X0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['4', '6'])).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i]:
% 0.47/0.68         (((X26) = (k1_xboole_0))
% 0.47/0.68          | ((sk_C_1 @ X27 @ X26) != (X27))
% 0.47/0.68          | ((X26) = (k1_tarski @ X27)))),
% 0.47/0.68      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (((X0) != (X1))
% 0.47/0.68          | ((k3_xboole_0 @ X2 @ (k1_tarski @ X0)) = (k1_tarski @ X1))
% 0.47/0.68          | ((k3_xboole_0 @ X2 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.47/0.68          | ((k3_xboole_0 @ X2 @ (k1_tarski @ X0)) = (k1_tarski @ X1))
% 0.47/0.68          | ((k3_xboole_0 @ X2 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (![X1 : $i, X2 : $i]:
% 0.47/0.68         (((k3_xboole_0 @ X2 @ (k1_tarski @ X1)) = (k1_xboole_0))
% 0.47/0.68          | ((k3_xboole_0 @ X2 @ (k1_tarski @ X1)) = (k1_tarski @ X1)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.47/0.68        | ((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['10', '13'])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.68  thf(d7_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.47/0.68       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X8 : $i, X10 : $i]:
% 0.47/0.68         ((r1_xboole_0 @ X8 @ X10)
% 0.47/0.68          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['15', '18'])).
% 0.47/0.68  thf('20', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.47/0.68      inference('simplify', [status(thm)], ['19'])).
% 0.47/0.68  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
