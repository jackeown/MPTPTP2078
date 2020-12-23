%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1djP9n4sNW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:32 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  267 ( 357 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t4_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X32: $i,X33: $i] :
      ( ( X29
       != ( k1_setfam_1 @ X30 ) )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ( r2_hidden @ X33 @ X32 )
      | ~ ( r2_hidden @ X33 @ X29 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X33 @ ( k1_setfam_1 @ X30 ) )
      | ( r2_hidden @ X33 @ X32 )
      | ~ ( r2_hidden @ X32 @ X30 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B_1 ) ) @ sk_A )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X30: $i,X35: $i] :
      ( ( X35
       != ( k1_setfam_1 @ X30 ) )
      | ( X35 = k1_xboole_0 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('13',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ ( k1_tarski @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11','13','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1djP9n4sNW
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:09:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.65/2.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.65/2.83  % Solved by: fo/fo7.sh
% 2.65/2.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.65/2.83  % done 7545 iterations in 2.374s
% 2.65/2.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.65/2.83  % SZS output start Refutation
% 2.65/2.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.65/2.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.65/2.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.65/2.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.65/2.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.65/2.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.65/2.83  thf(sk_A_type, type, sk_A: $i).
% 2.65/2.83  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.65/2.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.65/2.83  thf(t4_setfam_1, conjecture,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 2.65/2.83  thf(zf_stmt_0, negated_conjecture,
% 2.65/2.83    (~( ![A:$i,B:$i]:
% 2.65/2.83        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )),
% 2.65/2.83    inference('cnf.neg', [status(esa)], [t4_setfam_1])).
% 2.65/2.83  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A)),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf(d3_tarski, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( r1_tarski @ A @ B ) <=>
% 2.65/2.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.65/2.83  thf('2', plain,
% 2.65/2.83      (![X3 : $i, X5 : $i]:
% 2.65/2.83         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.65/2.83      inference('cnf', [status(esa)], [d3_tarski])).
% 2.65/2.83  thf(d1_setfam_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 2.65/2.83         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 2.65/2.83       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 2.65/2.83         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 2.65/2.83           ( ![C:$i]:
% 2.65/2.83             ( ( r2_hidden @ C @ B ) <=>
% 2.65/2.83               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 2.65/2.83  thf('3', plain,
% 2.65/2.83      (![X29 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 2.65/2.83         (((X29) != (k1_setfam_1 @ X30))
% 2.65/2.83          | ~ (r2_hidden @ X32 @ X30)
% 2.65/2.83          | (r2_hidden @ X33 @ X32)
% 2.65/2.83          | ~ (r2_hidden @ X33 @ X29)
% 2.65/2.83          | ((X30) = (k1_xboole_0)))),
% 2.65/2.83      inference('cnf', [status(esa)], [d1_setfam_1])).
% 2.65/2.83  thf('4', plain,
% 2.65/2.83      (![X30 : $i, X32 : $i, X33 : $i]:
% 2.65/2.83         (((X30) = (k1_xboole_0))
% 2.65/2.83          | ~ (r2_hidden @ X33 @ (k1_setfam_1 @ X30))
% 2.65/2.83          | (r2_hidden @ X33 @ X32)
% 2.65/2.83          | ~ (r2_hidden @ X32 @ X30))),
% 2.65/2.83      inference('simplify', [status(thm)], ['3'])).
% 2.65/2.83  thf('5', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.65/2.83         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 2.65/2.83          | ~ (r2_hidden @ X2 @ X0)
% 2.65/2.83          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 2.65/2.83          | ((X0) = (k1_xboole_0)))),
% 2.65/2.83      inference('sup-', [status(thm)], ['2', '4'])).
% 2.65/2.83  thf('6', plain,
% 2.65/2.83      (![X0 : $i]:
% 2.65/2.83         (((sk_B_1) = (k1_xboole_0))
% 2.65/2.83          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B_1)) @ sk_A)
% 2.65/2.83          | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ X0))),
% 2.65/2.83      inference('sup-', [status(thm)], ['1', '5'])).
% 2.65/2.83  thf('7', plain,
% 2.65/2.83      (![X3 : $i, X5 : $i]:
% 2.65/2.83         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 2.65/2.83      inference('cnf', [status(esa)], [d3_tarski])).
% 2.65/2.83  thf('8', plain,
% 2.65/2.83      (((r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A)
% 2.65/2.83        | ((sk_B_1) = (k1_xboole_0))
% 2.65/2.83        | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A))),
% 2.65/2.83      inference('sup-', [status(thm)], ['6', '7'])).
% 2.65/2.83  thf('9', plain,
% 2.65/2.83      ((((sk_B_1) = (k1_xboole_0))
% 2.65/2.83        | (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A))),
% 2.65/2.83      inference('simplify', [status(thm)], ['8'])).
% 2.65/2.83  thf('10', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B_1) @ sk_A)),
% 2.65/2.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.65/2.83  thf('11', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.65/2.83      inference('clc', [status(thm)], ['9', '10'])).
% 2.65/2.83  thf('12', plain,
% 2.65/2.83      (![X30 : $i, X35 : $i]:
% 2.65/2.83         (((X35) != (k1_setfam_1 @ X30))
% 2.65/2.83          | ((X35) = (k1_xboole_0))
% 2.65/2.83          | ((X30) != (k1_xboole_0)))),
% 2.65/2.83      inference('cnf', [status(esa)], [d1_setfam_1])).
% 2.65/2.83  thf('13', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.65/2.83      inference('simplify', [status(thm)], ['12'])).
% 2.65/2.83  thf('14', plain,
% 2.65/2.83      (![X3 : $i, X5 : $i]:
% 2.65/2.83         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.65/2.83      inference('cnf', [status(esa)], [d3_tarski])).
% 2.65/2.83  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.65/2.83  thf('15', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 2.65/2.83      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.65/2.83  thf('16', plain,
% 2.65/2.83      (![X3 : $i, X5 : $i]:
% 2.65/2.83         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.65/2.83      inference('cnf', [status(esa)], [d3_tarski])).
% 2.65/2.83  thf('17', plain,
% 2.65/2.83      (![X3 : $i, X5 : $i]:
% 2.65/2.83         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 2.65/2.83      inference('cnf', [status(esa)], [d3_tarski])).
% 2.65/2.83  thf('18', plain,
% 2.65/2.83      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 2.65/2.83      inference('sup-', [status(thm)], ['16', '17'])).
% 2.65/2.83  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.65/2.83      inference('simplify', [status(thm)], ['18'])).
% 2.65/2.83  thf(l1_zfmisc_1, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.65/2.83  thf('20', plain,
% 2.65/2.83      (![X20 : $i, X21 : $i]:
% 2.65/2.83         ((r2_hidden @ X20 @ X21) | ~ (r1_tarski @ (k1_tarski @ X20) @ X21))),
% 2.65/2.83      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.65/2.83  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.65/2.83      inference('sup-', [status(thm)], ['19', '20'])).
% 2.65/2.83  thf(t3_xboole_0, axiom,
% 2.65/2.83    (![A:$i,B:$i]:
% 2.65/2.83     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.65/2.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.65/2.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.65/2.83            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.65/2.83  thf('22', plain,
% 2.65/2.83      (![X6 : $i, X8 : $i, X9 : $i]:
% 2.65/2.83         (~ (r2_hidden @ X8 @ X6)
% 2.65/2.83          | ~ (r2_hidden @ X8 @ X9)
% 2.65/2.83          | ~ (r1_xboole_0 @ X6 @ X9))),
% 2.65/2.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.65/2.83  thf('23', plain,
% 2.65/2.83      (![X0 : $i, X1 : $i]:
% 2.65/2.83         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 2.65/2.83      inference('sup-', [status(thm)], ['21', '22'])).
% 2.65/2.83  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.65/2.83      inference('sup-', [status(thm)], ['15', '23'])).
% 2.65/2.83  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.65/2.83      inference('sup-', [status(thm)], ['14', '24'])).
% 2.65/2.83  thf('26', plain, ($false),
% 2.65/2.83      inference('demod', [status(thm)], ['0', '11', '13', '25'])).
% 2.65/2.83  
% 2.65/2.83  % SZS output end Refutation
% 2.65/2.83  
% 2.65/2.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
