%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0tdMvplSXE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  90 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 479 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t37_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ B @ A )
        <=> ( v3_ordinal1 @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( r2_hidden @ B @ A )
          <=> ( v3_ordinal1 @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_ordinal1])).

thf('0',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ X21 @ sk_A )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_ordinal1,axiom,(
    ! [A: $i] :
      ~ ( ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ~ ( r1_tarski @ A @ B ) )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v3_ordinal1 @ B ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( v3_ordinal1 @ B )
       => ~ ( r1_tarski @ A @ B ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( zip_tseitin_0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( r2_hidden @ B @ A )
       => ( v3_ordinal1 @ B ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X20: $i] :
      ( ( v3_ordinal1 @ X20 )
      | ~ ( r2_hidden @ X20 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ sk_A )
      | ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X19: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_B @ X19 ) @ X19 )
      | ~ ( zip_tseitin_0 @ ( sk_B_1 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,(
    ~ ( zip_tseitin_0 @ ( sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ~ ( zip_tseitin_0 @ ( sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['16','19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0tdMvplSXE
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:43:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 61 iterations in 0.030s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.47  thf(t37_ordinal1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ~( ![B:$i]: ( ( r2_hidden @ B @ A ) <=> ( v3_ordinal1 @ B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t37_ordinal1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X21 : $i]: ((r2_hidden @ X21 @ sk_A) | ~ (v3_ordinal1 @ X21))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t36_ordinal1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ~( ( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( ~( r1_tarski @ A @ B ) ) ) ) & 
% 0.20/0.47          ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_1, axiom,
% 0.20/0.47    (![B:$i,A:$i]:
% 0.20/0.47     ( ( ( v3_ordinal1 @ B ) => ( ~( r1_tarski @ A @ B ) ) ) =>
% 0.20/0.47       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X15 @ X16) | (r1_tarski @ X16 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf(d3_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.47          | (r2_hidden @ X2 @ X4)
% 0.20/0.47          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X2 @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X2 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v3_ordinal1 @ X0)
% 0.20/0.47          | (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (zip_tseitin_0 @ X1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.47  thf(zf_stmt_2, axiom,
% 0.20/0.47    (![B:$i,A:$i]:
% 0.20/0.47     ( ( ( r2_hidden @ B @ A ) => ( v3_ordinal1 @ B ) ) =>
% 0.20/0.47       ( zip_tseitin_1 @ B @ A ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i]:
% 0.20/0.47         ((zip_tseitin_1 @ X17 @ X18) | (r2_hidden @ X17 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X20 : $i]: ((v3_ordinal1 @ X20) | ~ (r2_hidden @ X20 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]: ((zip_tseitin_1 @ X0 @ sk_A) | (v3_ordinal1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i]:
% 0.20/0.47         ((zip_tseitin_1 @ X17 @ X18) | ~ (v3_ordinal1 @ X17))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.47  thf('9', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_5, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ~( ( ![B:$i]: ( zip_tseitin_1 @ B @ A ) ) & 
% 0.20/0.47          ( ![B:$i]: ( zip_tseitin_0 @ B @ A ) ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X19 : $i]:
% 0.20/0.47         (~ (zip_tseitin_1 @ (sk_B @ X19) @ X19)
% 0.20/0.47          | ~ (zip_tseitin_0 @ (sk_B_1 @ X19) @ X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.47  thf('11', plain, (~ (zip_tseitin_0 @ (sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | ~ (v3_ordinal1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | ~ (v3_ordinal1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.47  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v3_ordinal1 @ X0) | ~ (r2_hidden @ (sk_B_1 @ sk_A) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((~ (v3_ordinal1 @ (sk_B_1 @ sk_A)) | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X15 @ X16) | (v3_ordinal1 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('18', plain, (~ (zip_tseitin_0 @ (sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('19', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('21', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
