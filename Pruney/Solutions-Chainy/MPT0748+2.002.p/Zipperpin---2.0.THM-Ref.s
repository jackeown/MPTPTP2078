%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p50EcXeHHX

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  29 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   98 ( 145 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t38_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t38_ordinal1])).

thf('0',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ X4 @ sk_A )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
    ! [C: $i] :
      ( ( r2_hidden @ C @ B )
    <=> ( ( r2_hidden @ C @ A )
        & ( v3_ordinal1 @ C ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( sk_B @ X1 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_B @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t37_ordinal1,axiom,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ B @ A )
        <=> ( v3_ordinal1 @ B ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ ( sk_B_1 @ X3 ) )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t37_ordinal1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_B_1 @ ( sk_B @ X0 ) ) )
      | ( v3_ordinal1 @ ( sk_B_1 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( v3_ordinal1 @ ( sk_B_1 @ ( sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X3: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_B_1 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t37_ordinal1])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_B_1 @ ( sk_B @ X0 ) ) @ ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v3_ordinal1 @ ( sk_B_1 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( v3_ordinal1 @ ( sk_B_1 @ ( sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p50EcXeHHX
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 11 iterations in 0.011s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(t38_ordinal1, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ~( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ~( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( r2_hidden @ B @ A ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t38_ordinal1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X4 : $i]: ((r2_hidden @ X4 @ sk_A) | ~ (v3_ordinal1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(s1_xboole_0__e3_53__ordinal1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ?[B:$i]:
% 0.22/0.47       ( ![C:$i]:
% 0.22/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.47           ( ( r2_hidden @ C @ A ) & ( v3_ordinal1 @ C ) ) ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i]:
% 0.22/0.47         ((r2_hidden @ X2 @ (sk_B @ X1))
% 0.22/0.47          | ~ (v3_ordinal1 @ X2)
% 0.22/0.47          | ~ (r2_hidden @ X2 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [s1_xboole_0__e3_53__ordinal1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v3_ordinal1 @ X0)
% 0.22/0.47          | ~ (v3_ordinal1 @ X0)
% 0.22/0.47          | (r2_hidden @ X0 @ (sk_B @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ (sk_B @ sk_A)) | ~ (v3_ordinal1 @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.47  thf(t37_ordinal1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         ((v3_ordinal1 @ (sk_B_1 @ X3)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t37_ordinal1])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((v3_ordinal1 @ X0) | ~ (r2_hidden @ X0 @ (sk_B @ X1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [s1_xboole_0__e3_53__ordinal1])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((v3_ordinal1 @ (sk_B_1 @ (sk_B @ X0)))
% 0.22/0.47          | (v3_ordinal1 @ (sk_B_1 @ (sk_B @ X0))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('7', plain, (![X0 : $i]: (v3_ordinal1 @ (sk_B_1 @ (sk_B @ X0)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         (~ (v3_ordinal1 @ (sk_B_1 @ X3)) | ~ (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t37_ordinal1])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i]: ~ (r2_hidden @ (sk_B_1 @ (sk_B @ X0)) @ (sk_B @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('10', plain, (~ (v3_ordinal1 @ (sk_B_1 @ (sk_B @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['3', '9'])).
% 0.22/0.47  thf('11', plain, (![X0 : $i]: (v3_ordinal1 @ (sk_B_1 @ (sk_B @ X0)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.47  thf('12', plain, ($false), inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
