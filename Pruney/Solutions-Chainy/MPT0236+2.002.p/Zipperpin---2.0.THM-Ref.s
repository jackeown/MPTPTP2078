%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tg3JgkDcmC

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:58 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   36 (  64 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  345 ( 707 expanded)
%              Number of equality atoms :   36 (  74 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t31_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t31_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X6 ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('4',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X6 ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('5',plain,(
    ! [X6: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X11 )
      | ~ ( r2_hidden @ X11 @ X6 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X0 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ ( sk_D @ X10 @ X6 ) )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X6: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X11 )
      | ~ ( r2_hidden @ X11 @ X6 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tg3JgkDcmC
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:02:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.80/1.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.80/1.99  % Solved by: fo/fo7.sh
% 1.80/1.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/1.99  % done 305 iterations in 1.532s
% 1.80/1.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.80/1.99  % SZS output start Refutation
% 1.80/1.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.80/1.99  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.80/1.99  thf(sk_A_type, type, sk_A: $i).
% 1.80/1.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/1.99  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.80/1.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.80/1.99  thf(t31_zfmisc_1, conjecture,
% 1.80/1.99    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.80/1.99  thf(zf_stmt_0, negated_conjecture,
% 1.80/1.99    (~( ![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 1.80/1.99    inference('cnf.neg', [status(esa)], [t31_zfmisc_1])).
% 1.80/1.99  thf('0', plain, (((k3_tarski @ (k1_tarski @ sk_A)) != (sk_A))),
% 1.80/1.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/1.99  thf(d1_tarski, axiom,
% 1.80/1.99    (![A:$i,B:$i]:
% 1.80/1.99     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.80/1.99       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.80/1.99  thf('1', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/1.99         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 1.80/1.99      inference('cnf', [status(esa)], [d1_tarski])).
% 1.80/1.99  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/1.99      inference('simplify', [status(thm)], ['1'])).
% 1.80/1.99  thf(d4_tarski, axiom,
% 1.80/1.99    (![A:$i,B:$i]:
% 1.80/1.99     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.80/1.99       ( ![C:$i]:
% 1.80/1.99         ( ( r2_hidden @ C @ B ) <=>
% 1.80/1.99           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.80/1.99  thf('3', plain,
% 1.80/1.99      (![X6 : $i, X10 : $i]:
% 1.80/1.99         (((X10) = (k3_tarski @ X6))
% 1.80/1.99          | (r2_hidden @ (sk_D @ X10 @ X6) @ X6)
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 1.80/1.99      inference('cnf', [status(esa)], [d4_tarski])).
% 1.80/1.99  thf('4', plain,
% 1.80/1.99      (![X6 : $i, X10 : $i]:
% 1.80/1.99         (((X10) = (k3_tarski @ X6))
% 1.80/1.99          | (r2_hidden @ (sk_D @ X10 @ X6) @ X6)
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 1.80/1.99      inference('cnf', [status(esa)], [d4_tarski])).
% 1.80/1.99  thf('5', plain,
% 1.80/1.99      (![X6 : $i, X10 : $i, X11 : $i]:
% 1.80/1.99         (((X10) = (k3_tarski @ X6))
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X11)
% 1.80/1.99          | ~ (r2_hidden @ X11 @ X6)
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 1.80/1.99      inference('cnf', [status(esa)], [d4_tarski])).
% 1.80/1.99  thf('6', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 1.80/1.99          | ((X0) = (k3_tarski @ X1))
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 1.80/1.99          | ~ (r2_hidden @ X0 @ X1)
% 1.80/1.99          | ((X0) = (k3_tarski @ X1)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['4', '5'])).
% 1.80/1.99  thf('7', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X0 @ X1)
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 1.80/1.99          | ((X0) = (k3_tarski @ X1))
% 1.80/1.99          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 1.80/1.99      inference('simplify', [status(thm)], ['6'])).
% 1.80/1.99  thf('8', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 1.80/1.99          | ((X0) = (k3_tarski @ X1))
% 1.80/1.99          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 1.80/1.99          | ((X0) = (k3_tarski @ X1))
% 1.80/1.99          | ~ (r2_hidden @ X0 @ X1))),
% 1.80/1.99      inference('sup-', [status(thm)], ['3', '7'])).
% 1.80/1.99  thf('9', plain,
% 1.80/1.99      (![X0 : $i, X1 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X0 @ X1)
% 1.80/1.99          | ((X0) = (k3_tarski @ X1))
% 1.80/1.99          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 1.80/1.99      inference('simplify', [status(thm)], ['8'])).
% 1.80/1.99  thf('10', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r2_hidden @ (sk_D @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 1.80/1.99          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 1.80/1.99      inference('sup-', [status(thm)], ['2', '9'])).
% 1.80/1.99  thf('11', plain,
% 1.80/1.99      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.80/1.99         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 1.80/1.99      inference('cnf', [status(esa)], [d1_tarski])).
% 1.80/1.99  thf('12', plain,
% 1.80/1.99      (![X0 : $i, X3 : $i]:
% 1.80/1.99         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.80/1.99      inference('simplify', [status(thm)], ['11'])).
% 1.80/1.99  thf('13', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 1.80/1.99          | ((sk_D @ X0 @ (k1_tarski @ X0)) = (X0)))),
% 1.80/1.99      inference('sup-', [status(thm)], ['10', '12'])).
% 1.80/1.99  thf('14', plain,
% 1.80/1.99      (![X6 : $i, X10 : $i]:
% 1.80/1.99         (((X10) = (k3_tarski @ X6))
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X10 @ X6) @ (sk_D @ X10 @ X6))
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 1.80/1.99      inference('cnf', [status(esa)], [d4_tarski])).
% 1.80/1.99  thf('15', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         ((r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.80/1.99          | ((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.80/1.99          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 1.80/1.99      inference('sup+', [status(thm)], ['13', '14'])).
% 1.80/1.99  thf('16', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 1.80/1.99      inference('simplify', [status(thm)], ['15'])).
% 1.80/1.99  thf('17', plain,
% 1.80/1.99      (![X6 : $i, X10 : $i, X11 : $i]:
% 1.80/1.99         (((X10) = (k3_tarski @ X6))
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X11)
% 1.80/1.99          | ~ (r2_hidden @ X11 @ X6)
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X10 @ X6) @ X10))),
% 1.80/1.99      inference('cnf', [status(esa)], [d4_tarski])).
% 1.80/1.99  thf('18', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.80/1.99          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.80/1.99          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 1.80/1.99      inference('sup-', [status(thm)], ['16', '17'])).
% 1.80/1.99  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.80/1.99      inference('simplify', [status(thm)], ['1'])).
% 1.80/1.99  thf('20', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 1.80/1.99          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.80/1.99          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 1.80/1.99      inference('demod', [status(thm)], ['18', '19'])).
% 1.80/1.99  thf('21', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 1.80/1.99          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 1.80/1.99      inference('simplify', [status(thm)], ['20'])).
% 1.80/1.99  thf('22', plain,
% 1.80/1.99      (![X0 : $i]:
% 1.80/1.99         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 1.80/1.99          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 1.80/1.99      inference('simplify', [status(thm)], ['15'])).
% 1.80/1.99  thf('23', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 1.80/1.99      inference('clc', [status(thm)], ['21', '22'])).
% 1.80/1.99  thf('24', plain, (((sk_A) != (sk_A))),
% 1.80/1.99      inference('demod', [status(thm)], ['0', '23'])).
% 1.80/1.99  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 1.80/1.99  
% 1.80/1.99  % SZS output end Refutation
% 1.80/1.99  
% 1.80/2.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
