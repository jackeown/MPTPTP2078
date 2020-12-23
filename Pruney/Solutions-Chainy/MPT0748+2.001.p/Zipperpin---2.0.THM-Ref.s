%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bAYjqQO4xU

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  196 ( 293 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t36_ordinal1,axiom,(
    ! [A: $i] :
      ~ ( ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ~ ( r1_tarski @ A @ B ) )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v3_ordinal1 @ B ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( v3_ordinal1 @ B )
       => ~ ( r1_tarski @ A @ B ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( r2_hidden @ B @ A )
       => ( v3_ordinal1 @ B ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
    ! [C: $i] :
      ( ( r2_hidden @ C @ B )
    <=> ( ( r2_hidden @ C @ A )
        & ( v3_ordinal1 @ C ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( sk_B @ X0 ) )
      | ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( zip_tseitin_1 @ X5 @ X6 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ X1 @ ( sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i] :
      ~ ( ! [B: $i] :
            ( zip_tseitin_1 @ B @ A )
        & ! [B: $i] :
            ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_B_1 @ X7 ) @ X7 )
      | ~ ( zip_tseitin_0 @ ( sk_B_2 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ ( sk_B_2 @ ( sk_B @ X0 ) ) @ ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ X0 ) @ ( sk_B_2 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t38_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t38_ordinal1])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( r2_hidden @ X10 @ sk_A )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( sk_B @ X1 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_B @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( sk_B @ X1 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e3_53__ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ ( sk_B @ ( sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_B @ ( sk_B @ sk_A ) ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ ( sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v3_ordinal1 @ ( sk_B_2 @ ( sk_B @ ( sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ ( sk_B_2 @ ( sk_B @ X0 ) ) @ ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X0: $i] :
      ( v3_ordinal1 @ ( sk_B_2 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['18','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bAYjqQO4xU
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:28:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 26 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(t36_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( ~( r1_tarski @ A @ B ) ) ) ) & 
% 0.21/0.47          ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, axiom,
% 0.21/0.47    (![B:$i,A:$i]:
% 0.21/0.47     ( ( ( v3_ordinal1 @ B ) => ( ~( r1_tarski @ A @ B ) ) ) =>
% 0.21/0.47       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]: ((zip_tseitin_0 @ X3 @ X4) | (r1_tarski @ X4 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(zf_stmt_1, axiom,
% 0.21/0.47    (![B:$i,A:$i]:
% 0.21/0.47     ( ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) =>
% 0.21/0.47       ( zip_tseitin_1 @ B @ A ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]: ((zip_tseitin_1 @ X5 @ X6) | (r2_hidden @ X5 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf(s1_xboole_0__e3_53__ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ?[B:$i]:
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.47           ( ( r2_hidden @ C @ A ) & ( v3_ordinal1 @ C ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v3_ordinal1 @ X0) | ~ (r2_hidden @ X0 @ (sk_B @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [s1_xboole_0__e3_53__ordinal1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((zip_tseitin_1 @ X1 @ (sk_B @ X0)) | (v3_ordinal1 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]: ((zip_tseitin_1 @ X5 @ X6) | ~ (v3_ordinal1 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.47  thf('5', plain, (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ X1 @ (sk_B @ X0))),
% 0.21/0.47      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_4, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ![B:$i]: ( zip_tseitin_1 @ B @ A ) ) & 
% 0.21/0.47          ( ![B:$i]: ( zip_tseitin_0 @ B @ A ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         (~ (zip_tseitin_1 @ (sk_B_1 @ X7) @ X7)
% 0.21/0.47          | ~ (zip_tseitin_0 @ (sk_B_2 @ X7) @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]: ~ (zip_tseitin_0 @ (sk_B_2 @ (sk_B @ X0)) @ (sk_B @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]: (r1_tarski @ (sk_B @ X0) @ (sk_B_2 @ (sk_B @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.47  thf(t38_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_5, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ~( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( r2_hidden @ B @ A ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t38_ordinal1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X10 : $i]: ((r2_hidden @ X10 @ sk_A) | ~ (v3_ordinal1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ X2 @ (sk_B @ X1))
% 0.21/0.47          | ~ (v3_ordinal1 @ X2)
% 0.21/0.47          | ~ (r2_hidden @ X2 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [s1_xboole_0__e3_53__ordinal1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X0)
% 0.21/0.47          | ~ (v3_ordinal1 @ X0)
% 0.21/0.47          | (r2_hidden @ X0 @ (sk_B @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ (sk_B @ sk_A)) | ~ (v3_ordinal1 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ X2 @ (sk_B @ X1))
% 0.21/0.47          | ~ (v3_ordinal1 @ X2)
% 0.21/0.47          | ~ (r2_hidden @ X2 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [s1_xboole_0__e3_53__ordinal1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X0)
% 0.21/0.47          | ~ (v3_ordinal1 @ X0)
% 0.21/0.47          | (r2_hidden @ X0 @ (sk_B @ (sk_B @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ (sk_B @ (sk_B @ sk_A))) | ~ (v3_ordinal1 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf(t7_ordinal1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X0) | ~ (r1_tarski @ (sk_B @ (sk_B @ sk_A)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, (~ (v3_ordinal1 @ (sk_B_2 @ (sk_B @ (sk_B @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]: ((zip_tseitin_0 @ X3 @ X4) | (v3_ordinal1 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]: ~ (zip_tseitin_0 @ (sk_B_2 @ (sk_B @ X0)) @ (sk_B @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('21', plain, (![X0 : $i]: (v3_ordinal1 @ (sk_B_2 @ (sk_B @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, ($false), inference('demod', [status(thm)], ['18', '21'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
