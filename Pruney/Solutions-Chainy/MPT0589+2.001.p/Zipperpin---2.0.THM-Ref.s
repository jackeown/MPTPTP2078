%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wItvSnDJ2a

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  153 ( 162 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t193_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t193_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
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

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wItvSnDJ2a
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 35 iterations in 0.043s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(t193_relat_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t193_relat_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d3_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf(d4_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X13 @ X12)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.21/0.49          | ((X12) != (k1_relat_1 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X11 : $i, X13 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.21/0.49          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.21/0.49          | (r2_hidden @ 
% 0.21/0.49             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.21/0.49              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.21/0.49             X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.49  thf(l54_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((r2_hidden @ X4 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 0.21/0.49          | (r2_hidden @ 
% 0.21/0.49             (sk_C @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)
% 0.21/0.49          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.49  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
