%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDhym2vm22

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  36 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  160 ( 237 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k3_mcart_1 @ X35 @ X36 @ X37 )
      = ( k4_tarski @ ( k4_tarski @ X35 @ X36 ) @ X37 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X34
       != ( k1_tarski @ ( k4_tarski @ X32 @ X33 ) ) )
      | ( ( k1_relat_1 @ X34 )
        = ( k1_tarski @ X32 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t23_relat_1])).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X32 @ X33 ) ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X32 @ X33 ) ) )
        = ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X28 @ X29 ) @ ( k4_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X32 @ X33 ) ) )
      = ( k1_tarski @ X32 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X32 @ X33 ) ) )
      = ( k1_tarski @ X32 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('10',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','8','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDhym2vm22
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:26:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 24 iterations in 0.018s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(t97_mcart_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( k1_relat_1 @
% 0.19/0.47         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.19/0.47       ( k1_tarski @ A ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( k1_relat_1 @
% 0.19/0.47            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.19/0.47          ( k1_tarski @ A ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (((k1_relat_1 @ 
% 0.19/0.47         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.19/0.47         != (k1_tarski @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d3_mcart_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.19/0.47         ((k3_mcart_1 @ X35 @ X36 @ X37)
% 0.19/0.47           = (k4_tarski @ (k4_tarski @ X35 @ X36) @ X37))),
% 0.19/0.47      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.47  thf(t23_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ C ) =>
% 0.19/0.47       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 0.19/0.47         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 0.19/0.47           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.47         (((X34) != (k1_tarski @ (k4_tarski @ X32 @ X33)))
% 0.19/0.47          | ((k1_relat_1 @ X34) = (k1_tarski @ X32))
% 0.19/0.47          | ~ (v1_relat_1 @ X34))),
% 0.19/0.47      inference('cnf', [status(esa)], [t23_relat_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X32 : $i, X33 : $i]:
% 0.19/0.47         (~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X32 @ X33)))
% 0.19/0.47          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X32 @ X33)))
% 0.19/0.47              = (k1_tarski @ X32)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.47  thf(t69_enumset1, axiom,
% 0.19/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.47  thf('4', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.47  thf(fc7_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.47     ( v1_relat_1 @
% 0.19/0.47       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.47         (v1_relat_1 @ 
% 0.19/0.47          (k2_tarski @ (k4_tarski @ X28 @ X29) @ (k4_tarski @ X30 @ X31)))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X32 : $i, X33 : $i]:
% 0.19/0.47         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X32 @ X33)))
% 0.19/0.47           = (k1_tarski @ X32))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.19/0.47           = (k1_tarski @ (k4_tarski @ X2 @ X1)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '7'])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X32 : $i, X33 : $i]:
% 0.19/0.47         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X32 @ X33)))
% 0.19/0.47           = (k1_tarski @ X32))),
% 0.19/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.47  thf('10', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '8', '9'])).
% 0.19/0.47  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
