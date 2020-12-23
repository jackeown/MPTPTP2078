%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MZw5fiS0cw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:56 EST 2020

% Result     : Theorem 3.91s
% Output     : Refutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 224 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t100_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_zfmisc_1 @ ( k3_tarski @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k3_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( sk_C @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MZw5fiS0cw
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.91/4.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.91/4.14  % Solved by: fo/fo7.sh
% 3.91/4.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.91/4.14  % done 599 iterations in 3.728s
% 3.91/4.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.91/4.14  % SZS output start Refutation
% 3.91/4.14  thf(sk_A_type, type, sk_A: $i).
% 3.91/4.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.91/4.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.91/4.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.91/4.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.91/4.14  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.91/4.14  thf(t100_zfmisc_1, conjecture,
% 3.91/4.14    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 3.91/4.14  thf(zf_stmt_0, negated_conjecture,
% 3.91/4.14    (~( ![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )),
% 3.91/4.14    inference('cnf.neg', [status(esa)], [t100_zfmisc_1])).
% 3.91/4.14  thf('0', plain, (~ (r1_tarski @ sk_A @ (k1_zfmisc_1 @ (k3_tarski @ sk_A)))),
% 3.91/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.91/4.14  thf(d3_tarski, axiom,
% 3.91/4.14    (![A:$i,B:$i]:
% 3.91/4.14     ( ( r1_tarski @ A @ B ) <=>
% 3.91/4.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.91/4.14  thf('1', plain,
% 3.91/4.14      (![X1 : $i, X3 : $i]:
% 3.91/4.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.91/4.14      inference('cnf', [status(esa)], [d3_tarski])).
% 3.91/4.14  thf('2', plain,
% 3.91/4.14      (![X1 : $i, X3 : $i]:
% 3.91/4.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.91/4.14      inference('cnf', [status(esa)], [d3_tarski])).
% 3.91/4.14  thf(d4_tarski, axiom,
% 3.91/4.14    (![A:$i,B:$i]:
% 3.91/4.14     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 3.91/4.14       ( ![C:$i]:
% 3.91/4.14         ( ( r2_hidden @ C @ B ) <=>
% 3.91/4.14           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 3.91/4.14  thf('3', plain,
% 3.91/4.14      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 3.91/4.14         (~ (r2_hidden @ X9 @ X10)
% 3.91/4.14          | ~ (r2_hidden @ X11 @ X9)
% 3.91/4.14          | (r2_hidden @ X11 @ X12)
% 3.91/4.14          | ((X12) != (k3_tarski @ X10)))),
% 3.91/4.14      inference('cnf', [status(esa)], [d4_tarski])).
% 3.91/4.14  thf('4', plain,
% 3.91/4.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.91/4.14         ((r2_hidden @ X11 @ (k3_tarski @ X10))
% 3.91/4.14          | ~ (r2_hidden @ X11 @ X9)
% 3.91/4.14          | ~ (r2_hidden @ X9 @ X10))),
% 3.91/4.14      inference('simplify', [status(thm)], ['3'])).
% 3.91/4.14  thf('5', plain,
% 3.91/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.91/4.14         ((r1_tarski @ X0 @ X1)
% 3.91/4.14          | ~ (r2_hidden @ X0 @ X2)
% 3.91/4.14          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 3.91/4.14      inference('sup-', [status(thm)], ['2', '4'])).
% 3.91/4.14  thf('6', plain,
% 3.91/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.91/4.14         ((r1_tarski @ X0 @ X1)
% 3.91/4.14          | (r2_hidden @ (sk_C @ X2 @ (sk_C @ X1 @ X0)) @ (k3_tarski @ X0))
% 3.91/4.14          | (r1_tarski @ (sk_C @ X1 @ X0) @ X2))),
% 3.91/4.14      inference('sup-', [status(thm)], ['1', '5'])).
% 3.91/4.14  thf('7', plain,
% 3.91/4.14      (![X1 : $i, X3 : $i]:
% 3.91/4.14         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.91/4.14      inference('cnf', [status(esa)], [d3_tarski])).
% 3.91/4.14  thf('8', plain,
% 3.91/4.14      (![X0 : $i, X1 : $i]:
% 3.91/4.14         ((r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0))
% 3.91/4.14          | (r1_tarski @ X0 @ X1)
% 3.91/4.14          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 3.91/4.14      inference('sup-', [status(thm)], ['6', '7'])).
% 3.91/4.14  thf('9', plain,
% 3.91/4.14      (![X0 : $i, X1 : $i]:
% 3.91/4.14         ((r1_tarski @ X0 @ X1)
% 3.91/4.14          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 3.91/4.14      inference('simplify', [status(thm)], ['8'])).
% 3.91/4.14  thf(d1_zfmisc_1, axiom,
% 3.91/4.14    (![A:$i,B:$i]:
% 3.91/4.14     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 3.91/4.14       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 3.91/4.14  thf('10', plain,
% 3.91/4.14      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.91/4.14         (~ (r1_tarski @ X4 @ X5)
% 3.91/4.14          | (r2_hidden @ X4 @ X6)
% 3.91/4.14          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 3.91/4.14      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.91/4.14  thf('11', plain,
% 3.91/4.14      (![X4 : $i, X5 : $i]:
% 3.91/4.14         ((r2_hidden @ X4 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X4 @ X5))),
% 3.91/4.14      inference('simplify', [status(thm)], ['10'])).
% 3.91/4.14  thf('12', plain,
% 3.91/4.14      (![X0 : $i, X1 : $i]:
% 3.91/4.14         ((r1_tarski @ X0 @ X1)
% 3.91/4.14          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 3.91/4.14      inference('sup-', [status(thm)], ['9', '11'])).
% 3.91/4.14  thf('13', plain,
% 3.91/4.14      (![X1 : $i, X3 : $i]:
% 3.91/4.14         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.91/4.14      inference('cnf', [status(esa)], [d3_tarski])).
% 3.91/4.14  thf('14', plain,
% 3.91/4.14      (![X0 : $i]:
% 3.91/4.14         ((r1_tarski @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 3.91/4.14          | (r1_tarski @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 3.91/4.14      inference('sup-', [status(thm)], ['12', '13'])).
% 3.91/4.14  thf('15', plain,
% 3.91/4.14      (![X0 : $i]: (r1_tarski @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))),
% 3.91/4.14      inference('simplify', [status(thm)], ['14'])).
% 3.91/4.14  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 3.91/4.14  
% 3.91/4.14  % SZS output end Refutation
% 3.91/4.14  
% 3.91/4.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
