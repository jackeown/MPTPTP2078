%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EymJuW92rD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  182 ( 230 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t207_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_xboole_0 @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t207_relat_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 )
      | ( ( k7_relat_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EymJuW92rD
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 20 iterations in 0.014s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.44  thf(t207_relat_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ C ) =>
% 0.20/0.44       ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.44         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.44        ( ( v1_relat_1 @ C ) =>
% 0.20/0.44          ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.44            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t207_relat_1])).
% 0.20/0.44  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t83_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i]:
% 0.20/0.44         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.44  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.44  thf(t87_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) =>
% 0.20/0.44       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X8 : $i, X9 : $i]:
% 0.20/0.44         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.20/0.44          | ~ (v1_relat_1 @ X8))),
% 0.20/0.44      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.44  thf(t106_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.44       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((r1_xboole_0 @ X0 @ X2)
% 0.20/0.44          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X2)
% 0.20/0.44          | (r1_xboole_0 @ 
% 0.20/0.44             (k1_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf(t95_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) =>
% 0.20/0.44       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.44         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X10 : $i, X11 : $i]:
% 0.20/0.44         (~ (r1_xboole_0 @ (k1_relat_1 @ X10) @ X11)
% 0.20/0.44          | ((k7_relat_1 @ X10 @ X11) = (k1_xboole_0))
% 0.20/0.44          | ~ (v1_relat_1 @ X10))),
% 0.20/0.44      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X2)
% 0.20/0.44          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.20/0.44          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 0.20/0.44              = (k1_xboole_0)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.44  thf(dt_k7_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X6 : $i, X7 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         (((k7_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 0.20/0.44            = (k1_xboole_0))
% 0.20/0.44          | ~ (v1_relat_1 @ X2))),
% 0.20/0.44      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B) = (k1_xboole_0))
% 0.20/0.44          | ~ (v1_relat_1 @ X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['2', '9'])).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.44      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('14', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
