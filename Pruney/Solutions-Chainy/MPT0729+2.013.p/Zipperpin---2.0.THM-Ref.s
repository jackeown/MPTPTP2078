%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vfWQL8u8h7

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:42 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 ( 339 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('1',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k1_ordinal1 @ X13 )
      = ( k2_xboole_0 @ X13 @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('22',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vfWQL8u8h7
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 422 iterations in 0.312s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.58/0.77  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.58/0.77  thf('0', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.58/0.77      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.58/0.77  thf(t12_ordinal1, conjecture,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i]:
% 0.58/0.77        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.58/0.77  thf('1', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(d1_ordinal1, axiom,
% 0.58/0.77    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X13 : $i]:
% 0.58/0.77         ((k1_ordinal1 @ X13) = (k2_xboole_0 @ X13 @ (k1_tarski @ X13)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.58/0.77  thf(d3_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.58/0.77       ( ![D:$i]:
% 0.58/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.77           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X6 @ X4)
% 0.58/0.77          | (r2_hidden @ X6 @ X5)
% 0.58/0.77          | (r2_hidden @ X6 @ X3)
% 0.58/0.77          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.58/0.77         ((r2_hidden @ X6 @ X3)
% 0.58/0.77          | (r2_hidden @ X6 @ X5)
% 0.58/0.77          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['3'])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.58/0.77          | (r2_hidden @ X1 @ X0)
% 0.58/0.77          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['2', '4'])).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))
% 0.58/0.77          | (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.58/0.77          | (r2_hidden @ X0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '5'])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '6'])).
% 0.58/0.77  thf('8', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('9', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.58/0.77      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.58/0.77  thf('10', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.58/0.77          | (r2_hidden @ X1 @ X0)
% 0.58/0.77          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['2', '4'])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf(d1_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X11 @ X10)
% 0.58/0.77          | ((X11) = (X8))
% 0.58/0.77          | ((X10) != (k1_tarski @ X8)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X8 : $i, X11 : $i]:
% 0.58/0.77         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.77  thf('15', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['12', '14'])).
% 0.58/0.77  thf('16', plain, (((sk_A) != (sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('17', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf(antisymmetry_r2_hidden, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.77      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.58/0.77  thf('19', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.58/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.77  thf('20', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.58/0.77      inference('clc', [status(thm)], ['7', '19'])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X8 : $i, X11 : $i]:
% 0.58/0.77         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.77  thf('22', plain, (((sk_A) = (sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('23', plain, (((sk_A) != (sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('24', plain, ($false),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
