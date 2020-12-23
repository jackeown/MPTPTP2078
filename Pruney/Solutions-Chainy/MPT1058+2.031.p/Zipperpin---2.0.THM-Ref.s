%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V21FNjBLUj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  197 ( 269 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k3_xboole_0 @ X20 @ ( k10_relat_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('1',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V21FNjBLUj
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 30 iterations in 0.012s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.46  thf(t139_funct_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ C ) =>
% 0.21/0.46       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.46         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.46         (((k10_relat_1 @ (k7_relat_1 @ X21 @ X20) @ X22)
% 0.21/0.46            = (k3_xboole_0 @ X20 @ (k10_relat_1 @ X21 @ X22)))
% 0.21/0.46          | ~ (v1_relat_1 @ X21))),
% 0.21/0.46      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.46  thf(t175_funct_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.46       ( ![B:$i,C:$i]:
% 0.21/0.46         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.46           ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.46             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.46          ( ![B:$i,C:$i]:
% 0.21/0.46            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.46              ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.46                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.46         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.46          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf(t48_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.21/0.46           = (k3_xboole_0 @ X5 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.46  thf('4', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t85_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X13 @ X14)
% 0.21/0.46          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf(t83_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i]:
% 0.21/0.46         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.21/0.46           (k4_xboole_0 @ X0 @ sk_B)) = (k10_relat_1 @ sk_A @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (((k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.46         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.21/0.46      inference('sup+', [status(thm)], ['3', '8'])).
% 0.21/0.46  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.21/0.46         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (((k10_relat_1 @ sk_A @ sk_C) != (k10_relat_1 @ sk_A @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '11', '12'])).
% 0.21/0.46  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
