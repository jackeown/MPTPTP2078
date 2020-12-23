%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8l83bFqda

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  327 ( 608 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ( r1_xboole_0 @ ( k2_tarski @ X37 @ X39 ) @ X38 )
      | ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ ( k2_zfmisc_1 @ X35 @ X36 ) )
      | ~ ( r1_xboole_0 @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t131_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( A != B )
       => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
          & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_zfmisc_1])).

thf('6',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X33 @ X34 ) @ ( k2_zfmisc_1 @ X35 @ X36 ) )
      | ~ ( r1_xboole_0 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['6'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('23',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8l83bFqda
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 57 iterations in 0.030s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('0', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(t57_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.21/0.48          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.48         ((r2_hidden @ X37 @ X38)
% 0.21/0.48          | (r1_xboole_0 @ (k2_tarski @ X37 @ X39) @ X38)
% 0.21/0.48          | (r2_hidden @ X39 @ X38))),
% 0.21/0.48      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.21/0.48          | (r2_hidden @ X0 @ X1)
% 0.21/0.48          | (r2_hidden @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf(t127_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34) @ (k2_zfmisc_1 @ X35 @ X36))
% 0.21/0.48          | ~ (r1_xboole_0 @ X34 @ X36))),
% 0.21/0.48      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((r2_hidden @ X1 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.21/0.48             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf(t131_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( A ) != ( B ) ) =>
% 0.21/0.48       ( ( r1_xboole_0 @
% 0.21/0.48           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.48           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.21/0.48         ( r1_xboole_0 @
% 0.21/0.48           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.48           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( ( A ) != ( B ) ) =>
% 0.21/0.48          ( ( r1_xboole_0 @
% 0.21/0.48              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.48              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.21/0.48            ( r1_xboole_0 @
% 0.21/0.48              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.48              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))
% 0.21/0.48        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.48             (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.48           (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.21/0.48      inference('split', [status(esa)], ['6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k2_zfmisc_1 @ X33 @ X34) @ (k2_zfmisc_1 @ X35 @ X36))
% 0.21/0.48          | ~ (r1_xboole_0 @ X33 @ X35))),
% 0.21/0.48      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((r2_hidden @ X1 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X3) @ 
% 0.21/0.48             (k2_zfmisc_1 @ X0 @ X2)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['6'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i]:
% 0.21/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((sk_A) = (sk_B)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.48  thf('16', plain, (((sk_A) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.21/0.48      inference('split', [status(esa)], ['6'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.48          (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['7', '19'])).
% 0.21/0.48  thf('21', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i]:
% 0.21/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('23', plain, (((sk_A) = (sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, (((sk_A) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
