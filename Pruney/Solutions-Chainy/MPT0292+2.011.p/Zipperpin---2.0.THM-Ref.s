%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wO0EHQqPxC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:56 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   49 (  50 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 ( 285 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X18 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X5 @ X6 @ X7 )
      = ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k2_tarski @ X27 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ X26 ) )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ ( sk_C_1 @ X33 @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X33 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wO0EHQqPxC
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 166 iterations in 0.080s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.53  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.53  thf(t99_zfmisc_1, conjecture,
% 0.37/0.53    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t99_zfmisc_1])).
% 0.37/0.53  thf('0', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_A)) != (sk_A))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(t80_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.53  thf('1', plain,
% 0.37/0.53      (![X31 : $i]: (r1_tarski @ (k1_tarski @ X31) @ (k1_zfmisc_1 @ X31))),
% 0.37/0.53      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.37/0.53  thf(t77_enumset1, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X18 : $i, X19 : $i]:
% 0.37/0.53         ((k2_enumset1 @ X18 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.37/0.53      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.37/0.53  thf(t71_enumset1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.53         ((k2_enumset1 @ X5 @ X5 @ X6 @ X7) = (k1_enumset1 @ X5 @ X6 @ X7))),
% 0.37/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X18 : $i, X19 : $i]:
% 0.37/0.53         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.37/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.53  thf(t76_enumset1, axiom,
% 0.37/0.53    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.53  thf('5', plain,
% 0.37/0.53      (![X17 : $i]: ((k1_enumset1 @ X17 @ X17 @ X17) = (k1_tarski @ X17))),
% 0.37/0.53      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.37/0.53  thf('6', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.53  thf(t38_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.37/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.53         ((r2_hidden @ X27 @ X28)
% 0.37/0.53          | ~ (r1_tarski @ (k2_tarski @ X27 @ X29) @ X28))),
% 0.37/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.37/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.53  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['1', '8'])).
% 0.37/0.53  thf(l49_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      (![X25 : $i, X26 : $i]:
% 0.37/0.53         ((r1_tarski @ X25 @ (k3_tarski @ X26)) | ~ (r2_hidden @ X25 @ X26))),
% 0.37/0.53      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.37/0.53  thf('11', plain,
% 0.37/0.53      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf(d8_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.53       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.53  thf('12', plain,
% 0.37/0.53      (![X0 : $i, X2 : $i]:
% 0.37/0.53         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.53      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.53  thf('13', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 0.37/0.53          | (r2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.53  thf(t94_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.37/0.53       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X32 : $i, X33 : $i]:
% 0.37/0.53         ((r1_tarski @ (k3_tarski @ X32) @ X33)
% 0.37/0.53          | (r2_hidden @ (sk_C_1 @ X33 @ X32) @ X32))),
% 0.37/0.53      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.37/0.53  thf(d1_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.37/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.37/0.53  thf('15', plain,
% 0.37/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X23 @ X22)
% 0.37/0.53          | (r1_tarski @ X23 @ X21)
% 0.37/0.53          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 0.37/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.37/0.53  thf('16', plain,
% 0.37/0.53      (![X21 : $i, X23 : $i]:
% 0.37/0.53         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.53  thf('17', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1)
% 0.37/0.53          | (r1_tarski @ (sk_C_1 @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.37/0.53  thf('18', plain,
% 0.37/0.53      (![X32 : $i, X33 : $i]:
% 0.37/0.53         ((r1_tarski @ (k3_tarski @ X32) @ X33)
% 0.37/0.53          | ~ (r1_tarski @ (sk_C_1 @ X33 @ X32) @ X33))),
% 0.37/0.53      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.37/0.53          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.53  thf('20', plain,
% 0.37/0.53      (![X0 : $i]: (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.37/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.53  thf(t60_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.37/0.53  thf('21', plain,
% 0.37/0.53      (![X3 : $i, X4 : $i]:
% 0.37/0.53         (~ (r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X4 @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.37/0.53  thf('22', plain,
% 0.37/0.53      (![X0 : $i]: ~ (r2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.53  thf('23', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['13', '22'])).
% 0.37/0.53  thf('24', plain, (((sk_A) != (sk_A))),
% 0.37/0.53      inference('demod', [status(thm)], ['0', '23'])).
% 0.37/0.53  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.37/0.53  
% 0.37/0.53  % SZS output end Refutation
% 0.37/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
