%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4rynWl5Zij

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  65 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 ( 521 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ X5 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ X0 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( sk_D @ sk_B @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( sk_D @ sk_B @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ ( sk_D @ sk_B @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ~ ( r1_tarski @ X4 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('18',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('21',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['3','6'])).

thf('22',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4rynWl5Zij
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:08:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 158 iterations in 0.101s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(idempotence_k2_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.54  thf('0', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.54  thf(t7_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.54  thf('2', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.54  thf(t48_zfmisc_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.22/0.54       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.54        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.22/0.54          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.22/0.54  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('4', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t38_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         ((r1_tarski @ (k2_tarski @ X8 @ X10) @ X11)
% 0.22/0.54          | ~ (r2_hidden @ X10 @ X11)
% 0.22/0.54          | ~ (r2_hidden @ X8 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.54          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.54  thf(t14_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.54         ( ![D:$i]:
% 0.22/0.54           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.22/0.54             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.22/0.54       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.54          | ~ (r1_tarski @ X5 @ X4)
% 0.22/0.54          | (r1_tarski @ X5 @ (sk_D @ X5 @ X4 @ X3))
% 0.22/0.54          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((sk_B) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ X0))
% 0.22/0.54          | (r1_tarski @ X0 @ (sk_D @ X0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (((r1_tarski @ sk_B @ (sk_D @ sk_B @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.22/0.54        | ((sk_B) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '9'])).
% 0.22/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (((r1_tarski @ sk_B @ (sk_D @ sk_B @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.22/0.54        | ((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))))),
% 0.22/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) != (sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((r1_tarski @ sk_B @ (sk_D @ sk_B @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['12', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.54          | ~ (r1_tarski @ X5 @ X4)
% 0.22/0.54          | ~ (r1_tarski @ X4 @ (sk_D @ X5 @ X4 @ X3))
% 0.22/0.54          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((((sk_B) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))
% 0.22/0.54        | ~ (r1_tarski @ sk_B @ sk_B)
% 0.22/0.54        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.54  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.54  thf('21', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) != (sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf('24', plain, ($false),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
