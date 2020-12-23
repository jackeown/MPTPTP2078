%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XrhccldigE

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:32 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
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

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t31_wellord2,conjecture,(
    ! [A: $i] :
      ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t31_wellord2])).

thf('0',plain,(
    ~ ( r4_relat_2 @ ( k1_wellord2 @ sk_A ) @ sk_A ) ),
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

thf(d12_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_2 @ X0 )
      | ( r4_relat_2 @ X0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(t5_wellord2,axiom,(
    ! [A: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord2])).

thf('9',plain,(
    ! [X0: $i] :
      ( r4_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XrhccldigE
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 11:32:15 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.24/0.38  % Number of cores: 8
% 0.24/0.38  % Python version: Python 3.6.8
% 0.24/0.38  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 7 iterations in 0.010s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.49  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.24/0.49  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.24/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.49  thf(t31_wellord2, conjecture,
% 0.24/0.49    (![A:$i]: ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i]: ( r4_relat_2 @ ( k1_wellord2 @ A ) @ A ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t31_wellord2])).
% 0.24/0.49  thf('0', plain, (~ (r4_relat_2 @ (k1_wellord2 @ sk_A) @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(d1_wellord2, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ B ) =>
% 0.24/0.49       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.24/0.49         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.24/0.49           ( ![C:$i,D:$i]:
% 0.24/0.49             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.24/0.49               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.24/0.49                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      (![X1 : $i, X2 : $i]:
% 0.24/0.49         (((X2) != (k1_wellord2 @ X1))
% 0.24/0.49          | ((k3_relat_1 @ X2) = (X1))
% 0.24/0.49          | ~ (v1_relat_1 @ X2))),
% 0.24/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X1 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.24/0.49          | ((k3_relat_1 @ (k1_wellord2 @ X1)) = (X1)))),
% 0.24/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.24/0.49  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.24/0.49  thf('3', plain, (![X5 : $i]: (v1_relat_1 @ (k1_wellord2 @ X5))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.24/0.49  thf('4', plain, (![X1 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X1)) = (X1))),
% 0.24/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.24/0.49  thf(d12_relat_2, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ A ) =>
% 0.24/0.49       ( ( v4_relat_2 @ A ) <=> ( r4_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (![X0 : $i]:
% 0.24/0.49         (~ (v4_relat_2 @ X0)
% 0.24/0.49          | (r4_relat_2 @ X0 @ (k3_relat_1 @ X0))
% 0.24/0.49          | ~ (v1_relat_1 @ X0))),
% 0.24/0.49      inference('cnf', [status(esa)], [d12_relat_2])).
% 0.24/0.49  thf('6', plain,
% 0.24/0.49      (![X0 : $i]:
% 0.24/0.49         ((r4_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.24/0.49          | ~ (v4_relat_2 @ (k1_wellord2 @ X0)))),
% 0.24/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('7', plain, (![X5 : $i]: (v1_relat_1 @ (k1_wellord2 @ X5))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.24/0.49  thf(t5_wellord2, axiom, (![A:$i]: ( v4_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.24/0.49  thf('8', plain, (![X6 : $i]: (v4_relat_2 @ (k1_wellord2 @ X6))),
% 0.24/0.49      inference('cnf', [status(esa)], [t5_wellord2])).
% 0.24/0.49  thf('9', plain, (![X0 : $i]: (r4_relat_2 @ (k1_wellord2 @ X0) @ X0)),
% 0.24/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.24/0.49  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
