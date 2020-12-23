%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KimzwiR3oN

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 230 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t93_mcart_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k11_relat_1 @ A @ ( k1_mcart_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k11_relat_1 @ A @ ( k1_mcart_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_mcart_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k11_relat_1 @ sk_A @ ( k1_mcart_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3
        = ( k4_tarski @ ( k1_mcart_1 @ X3 ) @ ( k2_mcart_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_B
      = ( k4_tarski @ ( k1_mcart_1 @ sk_B ) @ ( k2_mcart_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k4_tarski @ ( k1_mcart_1 @ sk_B ) @ ( k2_mcart_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k11_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k11_relat_1 @ X0 @ ( k1_mcart_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k11_relat_1 @ sk_A @ ( k1_mcart_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k11_relat_1 @ sk_A @ ( k1_mcart_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KimzwiR3oN
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 8 iterations in 0.009s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(t93_mcart_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( r2_hidden @ B @ A ) =>
% 0.19/0.46           ( r2_hidden @
% 0.19/0.46             ( k2_mcart_1 @ B ) @ ( k11_relat_1 @ A @ ( k1_mcart_1 @ B ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( v1_relat_1 @ A ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( r2_hidden @ B @ A ) =>
% 0.19/0.46              ( r2_hidden @
% 0.19/0.46                ( k2_mcart_1 @ B ) @ ( k11_relat_1 @ A @ ( k1_mcart_1 @ B ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t93_mcart_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (~ (r2_hidden @ (k2_mcart_1 @ sk_B) @ 
% 0.19/0.46          (k11_relat_1 @ sk_A @ (k1_mcart_1 @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('2', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t23_mcart_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( r2_hidden @ A @ B ) =>
% 0.19/0.46         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         (((X3) = (k4_tarski @ (k1_mcart_1 @ X3) @ (k2_mcart_1 @ X3)))
% 0.19/0.46          | ~ (v1_relat_1 @ X4)
% 0.19/0.46          | ~ (r2_hidden @ X3 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_A)
% 0.19/0.46        | ((sk_B) = (k4_tarski @ (k1_mcart_1 @ sk_B) @ (k2_mcart_1 @ sk_B))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (((sk_B) = (k4_tarski @ (k1_mcart_1 @ sk_B) @ (k2_mcart_1 @ sk_B)))),
% 0.19/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf(t204_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ C ) =>
% 0.19/0.46       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.19/0.46         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ X1)
% 0.19/0.46          | (r2_hidden @ X0 @ (k11_relat_1 @ X1 @ X2))
% 0.19/0.46          | ~ (v1_relat_1 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ sk_B @ X0)
% 0.19/0.46          | ~ (v1_relat_1 @ X0)
% 0.19/0.46          | (r2_hidden @ (k2_mcart_1 @ sk_B) @ 
% 0.19/0.46             (k11_relat_1 @ X0 @ (k1_mcart_1 @ sk_B))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (((r2_hidden @ (k2_mcart_1 @ sk_B) @ 
% 0.19/0.46         (k11_relat_1 @ sk_A @ (k1_mcart_1 @ sk_B)))
% 0.19/0.46        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.19/0.46  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      ((r2_hidden @ (k2_mcart_1 @ sk_B) @ 
% 0.19/0.46        (k11_relat_1 @ sk_A @ (k1_mcart_1 @ sk_B)))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
