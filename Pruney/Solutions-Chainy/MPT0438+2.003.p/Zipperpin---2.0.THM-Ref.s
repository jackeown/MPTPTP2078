%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x1w6eVIW6P

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  275 ( 338 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X6 ) @ ( sk_D @ X5 @ X6 ) ) @ X6 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X6 ) @ ( sk_D @ X5 @ X6 ) ) @ X6 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X2 ) ) )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X6 ) @ ( sk_D @ X5 @ X6 ) ) @ X5 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t21_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_relat_1])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x1w6eVIW6P
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 29 iterations in 0.031s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(d3_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.49           ( ![C:$i,D:$i]:
% 0.21/0.49             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.49               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X6) @ (sk_D @ X5 @ X6)) @ X6)
% 0.21/0.49          | (r1_tarski @ X6 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.49  thf(t20_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.49           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.49          | (r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.21/0.49          | ~ (v1_relat_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.49          | (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X6) @ (sk_D @ X5 @ X6)) @ X6)
% 0.21/0.49          | (r1_tarski @ X6 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.49          | (r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.21/0.49          | ~ (v1_relat_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_D @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.49          | (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.49  thf(l54_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.21/0.49          | ~ (r2_hidden @ X2 @ X4)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (r2_hidden @ X3 @ X2)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X1 @ X0)) @ 
% 0.21/0.49             (k2_zfmisc_1 @ X2 @ (k2_relat_1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_tarski @ X0 @ X1)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X3 @ X2)) @ 
% 0.21/0.49             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X2)))
% 0.21/0.49          | (r1_tarski @ X2 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X6) @ (sk_D @ X5 @ X6)) @ X5)
% 0.21/0.49          | (r1_tarski @ X6 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_tarski @ X0 @ 
% 0.21/0.49             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.49          | (r1_tarski @ X0 @ 
% 0.21/0.49             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (r1_tarski @ X0 @ 
% 0.21/0.49             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ X0 @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.49  thf(t21_relat_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( r1_tarski @
% 0.21/0.49         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( v1_relat_1 @ A ) =>
% 0.21/0.49          ( r1_tarski @
% 0.21/0.49            A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t21_relat_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (~ (r1_tarski @ sk_A @ 
% 0.21/0.49          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, (~ (v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ($false), inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
