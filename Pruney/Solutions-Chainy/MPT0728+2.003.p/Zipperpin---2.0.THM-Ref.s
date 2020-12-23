%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AQ1KUCm566

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  130 ( 130 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t10_ordinal1,conjecture,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t10_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X26 ) )
      | ( X25 != X26 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('3',plain,(
    ! [X26: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X26 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X31: $i] :
      ( ( k1_ordinal1 @ X31 )
      = ( k2_xboole_0 @ X31 @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AQ1KUCm566
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 17 iterations in 0.014s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(t10_ordinal1, conjecture,
% 0.21/0.46    (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t10_ordinal1])).
% 0.21/0.46  thf('0', plain, (~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(l27_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X17 : $i, X18 : $i]:
% 0.21/0.46         ((r1_xboole_0 @ (k1_tarski @ X17) @ X18) | (r2_hidden @ X17 @ X18))),
% 0.21/0.46      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.46  thf(t16_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.21/0.46          ( ( A ) = ( B ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X25 : $i, X26 : $i]:
% 0.21/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X26))
% 0.21/0.46          | ((X25) != (X26)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X26 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X26))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.46  thf(d1_ordinal1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X31 : $i]:
% 0.21/0.46         ((k1_ordinal1 @ X31) = (k2_xboole_0 @ X31 @ (k1_tarski @ X31)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.46  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.46  thf(t7_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.46  thf(d3_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.46          | (r2_hidden @ X2 @ X4)
% 0.21/0.46          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.21/0.46          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '11'])).
% 0.21/0.46  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
