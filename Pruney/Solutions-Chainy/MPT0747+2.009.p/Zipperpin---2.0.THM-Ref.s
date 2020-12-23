%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BYKG7CIR1X

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  126 ( 216 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( r2_hidden @ B @ A )
       => ( v3_ordinal1 @ B ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t37_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ B @ A )
        <=> ( v3_ordinal1 @ B ) ) )).

thf(zf_stmt_2,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( r2_hidden @ B @ A )
          <=> ( v3_ordinal1 @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_ordinal1])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( v3_ordinal1 @ X7 )
      | ~ ( r2_hidden @ X7 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ sk_A )
      | ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X2 @ X3 )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i] :
      ~ ( ! [B: $i] :
            ( zip_tseitin_1 @ B @ A )
        & ! [B: $i] :
            ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_B @ X4 ) @ X4 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,(
    ~ ( zip_tseitin_0 @ ( sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( r2_hidden @ X8 @ sk_A )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( zip_tseitin_0 @ ( sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('15',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['12','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BYKG7CIR1X
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 20 iterations in 0.012s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.46  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.46  thf(t36_ordinal1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ~( ( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( ~( r1_tarski @ A @ B ) ) ) ) & 
% 0.20/0.46          ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, axiom,
% 0.20/0.46    (![B:$i,A:$i]:
% 0.20/0.46     ( ( ( v3_ordinal1 @ B ) => ( ~( r1_tarski @ A @ B ) ) ) =>
% 0.20/0.46       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (r1_tarski @ X1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(zf_stmt_1, axiom,
% 0.20/0.46    (![B:$i,A:$i]:
% 0.20/0.46     ( ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) =>
% 0.20/0.46       ( zip_tseitin_1 @ B @ A ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]: ((zip_tseitin_1 @ X2 @ X3) | (r2_hidden @ X2 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.46  thf(t37_ordinal1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_2, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t37_ordinal1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X7 : $i]: ((v3_ordinal1 @ X7) | ~ (r2_hidden @ X7 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]: ((zip_tseitin_1 @ X0 @ sk_A) | (v3_ordinal1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]: ((zip_tseitin_1 @ X2 @ X3) | ~ (v3_ordinal1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.46  thf('5', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_A)),
% 0.20/0.46      inference('clc', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.20/0.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.46  thf(zf_stmt_5, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ~( ( ![B:$i]: ( zip_tseitin_1 @ B @ A ) ) & 
% 0.20/0.46          ( ![B:$i]: ( zip_tseitin_0 @ B @ A ) ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X4 : $i]:
% 0.20/0.46         (~ (zip_tseitin_1 @ (sk_B @ X4) @ X4)
% 0.20/0.46          | ~ (zip_tseitin_0 @ (sk_B_1 @ X4) @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.46  thf('7', plain, (~ (zip_tseitin_0 @ (sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain, ((r1_tarski @ sk_A @ (sk_B_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X8 : $i]: ((r2_hidden @ X8 @ sk_A) | ~ (v3_ordinal1 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.46  thf(t7_ordinal1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, (~ (v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v3_ordinal1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain, (~ (zip_tseitin_0 @ (sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('15', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, ($false), inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
