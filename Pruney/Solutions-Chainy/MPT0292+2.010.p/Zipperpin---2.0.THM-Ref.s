%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pnxMHXot4D

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  238 ( 248 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X41: $i] :
      ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X44 ) @ ( k3_tarski @ X45 ) )
      | ~ ( r1_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('12',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X42 ) @ X43 )
      | ( r2_hidden @ ( sk_C_1 @ X43 @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( r1_tarski @ X37 @ X35 )
      | ( X36
       != ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ X37 @ X35 )
      | ~ ( r2_hidden @ X37 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X42 ) @ X43 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X43 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pnxMHXot4D
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 53 iterations in 0.028s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(t99_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.46  thf('0', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_A)) != (sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t80_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X41 : $i]: (r1_tarski @ (k1_tarski @ X41) @ (k1_zfmisc_1 @ X41))),
% 0.20/0.46      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.20/0.46  thf(t95_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X44 : $i, X45 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X44) @ (k3_tarski @ X45))
% 0.20/0.46          | ~ (r1_tarski @ X44 @ X45))),
% 0.20/0.46      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (r1_tarski @ (k3_tarski @ (k1_tarski @ X0)) @ 
% 0.20/0.46          (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(t69_enumset1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.46  thf('4', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.46  thf(l51_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X39 : $i, X40 : $i]:
% 0.20/0.46         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.46      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.46  thf('7', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.46  thf('8', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '8'])).
% 0.20/0.46  thf(d8_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.46       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X0 : $i, X2 : $i]:
% 0.20/0.46         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 0.20/0.46          | (r2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf(t94_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.20/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X42 : $i, X43 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X42) @ X43)
% 0.20/0.46          | (r2_hidden @ (sk_C_1 @ X43 @ X42) @ X42))),
% 0.20/0.46      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.46  thf(d1_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X37 @ X36)
% 0.20/0.46          | (r1_tarski @ X37 @ X35)
% 0.20/0.46          | ((X36) != (k1_zfmisc_1 @ X35)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X35 : $i, X37 : $i]:
% 0.20/0.46         ((r1_tarski @ X37 @ X35) | ~ (r2_hidden @ X37 @ (k1_zfmisc_1 @ X35)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1)
% 0.20/0.46          | (r1_tarski @ (sk_C_1 @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X42 : $i, X43 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ X42) @ X43)
% 0.20/0.46          | ~ (r1_tarski @ (sk_C_1 @ X43 @ X42) @ X43))),
% 0.20/0.46      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.20/0.46          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X0 : $i]: (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.20/0.46      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.46  thf(t60_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (r1_tarski @ X4 @ X5) | ~ (r2_xboole_0 @ X5 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X0 : $i]: ~ (r2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.46  thf('21', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['11', '20'])).
% 0.20/0.46  thf('22', plain, (((sk_A) != (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '21'])).
% 0.20/0.46  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
