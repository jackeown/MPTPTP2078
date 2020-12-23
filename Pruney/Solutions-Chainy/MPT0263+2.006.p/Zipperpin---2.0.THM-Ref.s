%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iopl9dpNIv

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:31 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  245 ( 431 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X45 @ X44 )
      | ( X45 = X42 )
      | ( X44
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X42: $i,X45: $i] :
      ( ( X45 = X42 )
      | ~ ( r2_hidden @ X45 @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( r2_hidden @ X55 @ X54 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X53 @ X55 ) @ X54 )
        = ( k2_tarski @ X53 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_B )
        = ( k2_tarski @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iopl9dpNIv
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.03  % Solved by: fo/fo7.sh
% 0.82/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.03  % done 1449 iterations in 0.585s
% 0.82/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.03  % SZS output start Refutation
% 0.82/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.82/1.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.82/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.03  thf(t3_xboole_0, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.82/1.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.82/1.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.82/1.03            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.82/1.03  thf('0', plain,
% 0.82/1.03      (![X13 : $i, X14 : $i]:
% 0.82/1.03         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.82/1.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.82/1.03  thf(d1_tarski, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.82/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.82/1.03  thf('1', plain,
% 0.82/1.03      (![X42 : $i, X44 : $i, X45 : $i]:
% 0.82/1.03         (~ (r2_hidden @ X45 @ X44)
% 0.82/1.03          | ((X45) = (X42))
% 0.82/1.03          | ((X44) != (k1_tarski @ X42)))),
% 0.82/1.03      inference('cnf', [status(esa)], [d1_tarski])).
% 0.82/1.03  thf('2', plain,
% 0.82/1.03      (![X42 : $i, X45 : $i]:
% 0.82/1.03         (((X45) = (X42)) | ~ (r2_hidden @ X45 @ (k1_tarski @ X42)))),
% 0.82/1.03      inference('simplify', [status(thm)], ['1'])).
% 0.82/1.03  thf('3', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.82/1.03          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['0', '2'])).
% 0.82/1.03  thf('4', plain,
% 0.82/1.03      (![X13 : $i, X14 : $i]:
% 0.82/1.03         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 0.82/1.03      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.82/1.03  thf('5', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((r2_hidden @ X0 @ X1)
% 0.82/1.03          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.82/1.03          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.82/1.03      inference('sup+', [status(thm)], ['3', '4'])).
% 0.82/1.03  thf('6', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.82/1.03      inference('simplify', [status(thm)], ['5'])).
% 0.82/1.03  thf(t58_zfmisc_1, conjecture,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.82/1.03       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.82/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.03    (~( ![A:$i,B:$i]:
% 0.82/1.03        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.82/1.03          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.82/1.03    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.82/1.03  thf('7', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('8', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.82/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.82/1.03  thf('9', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.82/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.82/1.03  thf(t53_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.82/1.03       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.82/1.03  thf('10', plain,
% 0.82/1.03      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.82/1.03         (~ (r2_hidden @ X53 @ X54)
% 0.82/1.03          | ~ (r2_hidden @ X55 @ X54)
% 0.82/1.03          | ((k3_xboole_0 @ (k2_tarski @ X53 @ X55) @ X54)
% 0.82/1.03              = (k2_tarski @ X53 @ X55)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 0.82/1.03  thf('11', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k3_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_B)
% 0.82/1.03            = (k2_tarski @ sk_A @ X0))
% 0.82/1.03          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.82/1.03  thf('12', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf('13', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.82/1.03            = (k2_tarski @ sk_A @ X0))
% 0.82/1.03          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['11', '12'])).
% 0.82/1.03  thf('14', plain,
% 0.82/1.03      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.82/1.03         = (k2_tarski @ sk_A @ sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['8', '13'])).
% 0.82/1.03  thf(t69_enumset1, axiom,
% 0.82/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.82/1.03  thf('15', plain,
% 0.82/1.03      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.82/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.03  thf('16', plain,
% 0.82/1.03      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.82/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.03  thf('17', plain,
% 0.82/1.03      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.82/1.03      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.82/1.03  thf('18', plain,
% 0.82/1.03      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('19', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.03  thf('20', plain,
% 0.82/1.03      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.82/1.03      inference('demod', [status(thm)], ['18', '19'])).
% 0.82/1.03  thf('21', plain, ($false),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['17', '20'])).
% 0.82/1.03  
% 0.82/1.03  % SZS output end Refutation
% 0.82/1.03  
% 0.82/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
