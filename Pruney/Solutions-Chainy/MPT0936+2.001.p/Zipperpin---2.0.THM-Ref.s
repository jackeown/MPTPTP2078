%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8pplar1UGH

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:23 EST 2020

% Result     : Theorem 9.76s
% Output     : Refutation 9.76s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  137 ( 191 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_11_type,type,(
    sk_B_11: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('0',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B_11 @ sk_C_3 ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X164: $i,X165: $i,X166: $i] :
      ( ( k3_mcart_1 @ X164 @ X165 @ X166 )
      = ( k4_tarski @ ( k4_tarski @ X164 @ X165 ) @ X166 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X159: $i,X160: $i,X161: $i] :
      ( ( X161
       != ( k1_tarski @ ( k4_tarski @ X159 @ X160 ) ) )
      | ( ( k1_relat_1 @ X161 )
        = ( k1_tarski @ X159 ) )
      | ~ ( v1_relat_1 @ X161 ) ) ),
    inference(cnf,[status(esa)],[t23_relat_1])).

thf('3',plain,(
    ! [X159: $i,X160: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X159 @ X160 ) ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X159 @ X160 ) ) )
        = ( k1_tarski @ X159 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X155: $i,X156: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X155 @ X156 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_relat_1])).

thf('5',plain,(
    ! [X159: $i,X160: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X159 @ X160 ) ) )
      = ( k1_tarski @ X159 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X159: $i,X160: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X159 @ X160 ) ) )
      = ( k1_tarski @ X159 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('8',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','6','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8pplar1UGH
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 9.76/10.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.76/10.01  % Solved by: fo/fo7.sh
% 9.76/10.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.76/10.01  % done 6053 iterations in 9.543s
% 9.76/10.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.76/10.01  % SZS output start Refutation
% 9.76/10.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.76/10.01  thf(sk_B_11_type, type, sk_B_11: $i).
% 9.76/10.01  thf(sk_C_3_type, type, sk_C_3: $i).
% 9.76/10.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.76/10.01  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 9.76/10.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.76/10.01  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 9.76/10.01  thf(sk_A_type, type, sk_A: $i).
% 9.76/10.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 9.76/10.01  thf(t97_mcart_1, conjecture,
% 9.76/10.01    (![A:$i,B:$i,C:$i]:
% 9.76/10.01     ( ( k1_relat_1 @
% 9.76/10.01         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 9.76/10.01       ( k1_tarski @ A ) ))).
% 9.76/10.01  thf(zf_stmt_0, negated_conjecture,
% 9.76/10.01    (~( ![A:$i,B:$i,C:$i]:
% 9.76/10.01        ( ( k1_relat_1 @
% 9.76/10.01            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 9.76/10.01          ( k1_tarski @ A ) ) )),
% 9.76/10.01    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 9.76/10.01  thf('0', plain,
% 9.76/10.01      (((k1_relat_1 @ 
% 9.76/10.01         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B_11 @ sk_C_3))))
% 9.76/10.01         != (k1_tarski @ sk_A))),
% 9.76/10.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.76/10.01  thf(d3_mcart_1, axiom,
% 9.76/10.01    (![A:$i,B:$i,C:$i]:
% 9.76/10.01     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 9.76/10.01  thf('1', plain,
% 9.76/10.01      (![X164 : $i, X165 : $i, X166 : $i]:
% 9.76/10.01         ((k3_mcart_1 @ X164 @ X165 @ X166)
% 9.76/10.01           = (k4_tarski @ (k4_tarski @ X164 @ X165) @ X166))),
% 9.76/10.01      inference('cnf', [status(esa)], [d3_mcart_1])).
% 9.76/10.01  thf(t23_relat_1, axiom,
% 9.76/10.01    (![A:$i,B:$i,C:$i]:
% 9.76/10.01     ( ( v1_relat_1 @ C ) =>
% 9.76/10.01       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 9.76/10.01         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 9.76/10.01           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 9.76/10.01  thf('2', plain,
% 9.76/10.01      (![X159 : $i, X160 : $i, X161 : $i]:
% 9.76/10.01         (((X161) != (k1_tarski @ (k4_tarski @ X159 @ X160)))
% 9.76/10.01          | ((k1_relat_1 @ X161) = (k1_tarski @ X159))
% 9.76/10.01          | ~ (v1_relat_1 @ X161))),
% 9.76/10.01      inference('cnf', [status(esa)], [t23_relat_1])).
% 9.76/10.01  thf('3', plain,
% 9.76/10.01      (![X159 : $i, X160 : $i]:
% 9.76/10.01         (~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X159 @ X160)))
% 9.76/10.01          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X159 @ X160)))
% 9.76/10.01              = (k1_tarski @ X159)))),
% 9.76/10.01      inference('simplify', [status(thm)], ['2'])).
% 9.76/10.01  thf(fc5_relat_1, axiom,
% 9.76/10.01    (![A:$i,B:$i]: ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 9.76/10.01  thf('4', plain,
% 9.76/10.01      (![X155 : $i, X156 : $i]:
% 9.76/10.01         (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X155 @ X156)))),
% 9.76/10.01      inference('cnf', [status(esa)], [fc5_relat_1])).
% 9.76/10.01  thf('5', plain,
% 9.76/10.01      (![X159 : $i, X160 : $i]:
% 9.76/10.01         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X159 @ X160)))
% 9.76/10.01           = (k1_tarski @ X159))),
% 9.76/10.01      inference('demod', [status(thm)], ['3', '4'])).
% 9.76/10.01  thf('6', plain,
% 9.76/10.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.76/10.01         ((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 9.76/10.01           = (k1_tarski @ (k4_tarski @ X2 @ X1)))),
% 9.76/10.01      inference('sup+', [status(thm)], ['1', '5'])).
% 9.76/10.01  thf('7', plain,
% 9.76/10.01      (![X159 : $i, X160 : $i]:
% 9.76/10.01         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X159 @ X160)))
% 9.76/10.01           = (k1_tarski @ X159))),
% 9.76/10.01      inference('demod', [status(thm)], ['3', '4'])).
% 9.76/10.01  thf('8', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 9.76/10.01      inference('demod', [status(thm)], ['0', '6', '7'])).
% 9.76/10.01  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 9.76/10.01  
% 9.76/10.01  % SZS output end Refutation
% 9.76/10.01  
% 9.76/10.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
