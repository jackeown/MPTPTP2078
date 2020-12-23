%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YIWUIs9rUu

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  47 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 ( 337 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_setfam_1_type,type,(
    k2_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t29_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t29_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ ( k2_setfam_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k2_xboole_0 @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k2_xboole_0 @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ( X10
       != ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X8 @ X13 )
      | ( zip_tseitin_0 @ X9 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ X3 @ ( k2_xboole_0 @ X3 @ ( sk_C @ X1 @ X0 ) ) @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X3 @ X2 ) @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ X2 @ X0 )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X16 @ X19 )
      | ( X19
       != ( k2_setfam_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k2_setfam_1 @ X18 @ X17 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t17_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_setfam_1 @ X24 @ X25 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t17_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ X0 @ ( k2_setfam_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YIWUIs9rUu
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 39 iterations in 0.032s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(t29_setfam_1, conjecture,
% 0.20/0.48    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t29_setfam_1])).
% 0.20/0.48  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ (k2_setfam_1 @ sk_A @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('1', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf(t31_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.48  thf('2', plain, (![X5 : $i]: ((k3_tarski @ (k1_tarski @ X5)) = (X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.48  thf('3', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t93_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k3_tarski @ (k2_tarski @ X6 @ X7)) = (k2_xboole_0 @ X6 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.20/0.48  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf(d4_setfam_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.48           ( ?[E:$i,F:$i]:
% 0.20/0.48             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.48               ( ( D ) = ( k2_xboole_0 @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, axiom,
% 0.20/0.48    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.48       ( ( ( D ) = ( k2_xboole_0 @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.48         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X13)
% 0.20/0.48          | ~ (r2_hidden @ X8 @ X13)
% 0.20/0.48          | ~ (r2_hidden @ X9 @ X11)
% 0.20/0.48          | ((X10) != (k2_xboole_0 @ X8 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X11 : $i, X13 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X9 @ X11)
% 0.20/0.48          | ~ (r2_hidden @ X8 @ X13)
% 0.20/0.48          | (zip_tseitin_0 @ X9 @ X8 @ (k2_xboole_0 @ X8 @ X9) @ X11 @ X13))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X0 @ X1)
% 0.20/0.48          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ X3 @ 
% 0.20/0.48             (k2_xboole_0 @ X3 @ (sk_C @ X1 @ X0)) @ X0 @ X2)
% 0.20/0.48          | ~ (r2_hidden @ X3 @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X0 @ X1)
% 0.20/0.48          | (zip_tseitin_0 @ (sk_C @ X3 @ X2) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.48             (k2_xboole_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ X2 @ X0)
% 0.20/0.48          | (r1_tarski @ X2 @ X3))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.48           (sk_C @ X1 @ X0) @ X0 @ X0)
% 0.20/0.48          | (r1_tarski @ X0 @ X1)
% 0.20/0.48          | (r1_tarski @ X0 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_tarski @ X0 @ X1)
% 0.20/0.48          | (zip_tseitin_0 @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 0.20/0.48             (sk_C @ X1 @ X0) @ X0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_3, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( C ) = ( k2_setfam_1 @ A @ B ) ) <=>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.48           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.48          | (r2_hidden @ X16 @ X19)
% 0.20/0.48          | ((X19) != (k2_setfam_1 @ X18 @ X17)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         ((r2_hidden @ X16 @ (k2_setfam_1 @ X18 @ X17))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.20/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_tarski @ X0 @ X1)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_tarski @ X0 @ (k2_setfam_1 @ X0 @ X0))
% 0.20/0.48          | (r1_tarski @ X0 @ (k2_setfam_1 @ X0 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  thf(t17_setfam_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X24 : $i, X25 : $i]:
% 0.20/0.48         ((r1_setfam_1 @ X24 @ X25) | ~ (r1_tarski @ X24 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [t17_setfam_1])).
% 0.20/0.48  thf('21', plain, (![X0 : $i]: (r1_setfam_1 @ X0 @ (k2_setfam_1 @ X0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.34/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
