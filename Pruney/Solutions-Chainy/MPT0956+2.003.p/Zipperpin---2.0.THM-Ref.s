%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRfgrQoXWG

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 108 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t29_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord2])).

thf('0',plain,(
    ~ ( r1_relat_2 @ ( k1_wellord2 @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2
       != ( k1_wellord2 @ X1 ) )
      | ( ( k3_relat_1 @ X2 )
        = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d9_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ X0 )
      | ( r1_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(t2_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_wellord2])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRfgrQoXWG
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 7 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.20/0.46  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(t29_wellord2, conjecture,
% 0.20/0.46    (![A:$i]: ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]: ( r1_relat_2 @ ( k1_wellord2 @ A ) @ A ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t29_wellord2])).
% 0.20/0.46  thf('0', plain, (~ (r1_relat_2 @ (k1_wellord2 @ sk_A) @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d1_wellord2, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.46         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.46           ( ![C:$i,D:$i]:
% 0.20/0.46             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.46               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.46                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         (((X2) != (k1_wellord2 @ X1))
% 0.20/0.46          | ((k3_relat_1 @ X2) = (X1))
% 0.20/0.46          | ~ (v1_relat_1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X1 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.20/0.46          | ((k3_relat_1 @ (k1_wellord2 @ X1)) = (X1)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.46  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.46  thf('3', plain, (![X5 : $i]: (v1_relat_1 @ (k1_wellord2 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.46  thf('4', plain, (![X1 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X1)) = (X1))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(d9_relat_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( ( v1_relat_2 @ A ) <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_2 @ X0)
% 0.20/0.46          | (r1_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d9_relat_2])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.46          | ~ (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain, (![X5 : $i]: (v1_relat_1 @ (k1_wellord2 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.46  thf(t2_wellord2, axiom, (![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.46  thf('8', plain, (![X6 : $i]: (v1_relat_2 @ (k1_wellord2 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_wellord2])).
% 0.20/0.46  thf('9', plain, (![X0 : $i]: (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.46  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
