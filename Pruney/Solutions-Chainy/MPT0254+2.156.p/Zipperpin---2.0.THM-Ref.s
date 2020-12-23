%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Di5FQfqJ2y

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:55 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   50 (  98 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  268 ( 612 expanded)
%              Number of equality atoms :   16 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('3',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','4'])).

thf('6',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t47_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ X24 @ X26 ) @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t47_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

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

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','4'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X17 @ X20 )
      | ~ ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['16','28'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['13','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Di5FQfqJ2y
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 270 iterations in 0.096s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(t49_zfmisc_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t15_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.54       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (((X13) = (k1_xboole_0))
% 0.36/0.54          | ((k2_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf('4', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.54  thf('5', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '4'])).
% 0.36/0.54  thf('6', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('7', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf(t47_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.36/0.54       ( r2_hidden @ A @ C ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.54         ((r2_hidden @ X24 @ X25)
% 0.36/0.54          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_tarski @ X24 @ X26) @ X25) @ X25))),
% 0.36/0.54      inference('cnf', [status(esa)], [t47_zfmisc_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ X1)
% 0.36/0.54          | (r2_hidden @ X0 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 0.36/0.54          | (r2_hidden @ sk_A @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.36/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.54  thf('12', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.54  thf('13', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf('14', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf(t3_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.36/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X2 @ X0)
% 0.36/0.54          | ~ (r2_hidden @ X2 @ X3)
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf('17', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '4'])).
% 0.36/0.54  thf(t70_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.36/0.54            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.36/0.54       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.36/0.54            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X17 @ X20)
% 0.36/0.54          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r1_xboole_0 @ X0 @ k1_xboole_0) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.36/0.54  thf('20', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.36/0.54  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)),
% 0.36/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X2 @ X0)
% 0.36/0.54          | ~ (r2_hidden @ X2 @ X3)
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X0 @ X1)
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.36/0.54          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r1_xboole_0 @ X0 @ X1)
% 0.36/0.54          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.36/0.54          | (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.54  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ sk_B @ X0)),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '27'])).
% 0.36/0.54  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.36/0.54      inference('demod', [status(thm)], ['16', '28'])).
% 0.36/0.54  thf('30', plain, ($false), inference('sup-', [status(thm)], ['13', '29'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.41/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
