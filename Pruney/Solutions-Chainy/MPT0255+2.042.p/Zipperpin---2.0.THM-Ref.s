%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYOnYepzmp

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:01 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  231 ( 380 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','9'])).

thf('12',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYOnYepzmp
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 117 iterations in 0.072s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(t50_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.53        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf(d10_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.53  thf('4', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.35/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.53  thf(t38_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.35/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         ((r2_hidden @ X18 @ X19)
% 0.35/0.53          | ~ (r1_tarski @ (k2_tarski @ X18 @ X20) @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf(d3_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.35/0.53       ( ![D:$i]:
% 0.35/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.53           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.35/0.53          | (r2_hidden @ X2 @ X4)
% 0.35/0.53          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.35/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.35/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (r2_hidden @ X1 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '8'])).
% 0.35/0.53  thf('10', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.35/0.53      inference('sup+', [status(thm)], ['2', '9'])).
% 0.35/0.53  thf('11', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.35/0.53      inference('sup+', [status(thm)], ['2', '9'])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.35/0.53         ((r1_tarski @ (k2_tarski @ X18 @ X20) @ X21)
% 0.35/0.53          | ~ (r2_hidden @ X20 @ X21)
% 0.35/0.53          | ~ (r2_hidden @ X18 @ X21))),
% 0.35/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.35/0.53          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('14', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.35/0.53  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('16', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.35/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.53  thf(t12_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X11 : $i, X12 : $i]:
% 0.35/0.53         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.53  thf(t49_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X22 : $i, X23 : $i]:
% 0.35/0.53         ((k2_xboole_0 @ (k1_tarski @ X22) @ X23) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.53  thf('24', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['20', '23'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
