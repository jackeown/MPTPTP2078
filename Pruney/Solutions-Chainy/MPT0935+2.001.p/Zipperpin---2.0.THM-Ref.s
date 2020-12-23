%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vet7VY5dBB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  216 ( 302 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t96_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ D @ E @ F ) ) ) )
      = ( k2_tarski @ A @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ D @ E @ F ) ) ) )
        = ( k2_tarski @ A @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t96_mcart_1])).

thf('0',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_mcart_1 @ sk_D @ sk_E @ sk_F ) ) ) )
 != ( k2_tarski @ sk_A @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_mcart_1 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_mcart_1 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t24_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( v1_relat_1 @ E )
     => ( ( E
          = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) )
       => ( ( ( k1_relat_1 @ E )
            = ( k2_tarski @ A @ C ) )
          & ( ( k2_relat_1 @ E )
            = ( k2_tarski @ B @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X8
       != ( k2_tarski @ ( k4_tarski @ X4 @ X5 ) @ ( k4_tarski @ X6 @ X7 ) ) )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_tarski @ X4 @ X6 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X4 @ X5 ) @ ( k4_tarski @ X6 @ X7 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X4 @ X5 ) @ ( k4_tarski @ X6 @ X7 ) ) )
        = ( k2_tarski @ X4 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X0 @ X1 ) @ ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X4 @ X5 ) @ ( k4_tarski @ X6 @ X7 ) ) )
      = ( k2_tarski @ X4 @ X6 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ X3 @ X4 ) ) )
      = ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k3_mcart_1 @ X4 @ X3 @ X5 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k2_tarski @ ( k4_tarski @ X4 @ X3 ) @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X4 @ X5 ) @ ( k4_tarski @ X6 @ X7 ) ) )
      = ( k2_tarski @ X4 @ X6 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('10',plain,(
    ( k2_tarski @ sk_A @ sk_D )
 != ( k2_tarski @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['0','8','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vet7VY5dBB
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 17 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.46  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(t96_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.46     ( ( k1_relat_1 @
% 0.20/0.46         ( k1_relat_1 @
% 0.20/0.46           ( k2_tarski @
% 0.20/0.46             ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ D @ E @ F ) ) ) ) =
% 0.20/0.46       ( k2_tarski @ A @ D ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.46        ( ( k1_relat_1 @
% 0.20/0.46            ( k1_relat_1 @
% 0.20/0.46              ( k2_tarski @
% 0.20/0.46                ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ D @ E @ F ) ) ) ) =
% 0.20/0.46          ( k2_tarski @ A @ D ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t96_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k1_relat_1 @ 
% 0.20/0.46         (k1_relat_1 @ 
% 0.20/0.46          (k2_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.46           (k3_mcart_1 @ sk_D @ sk_E @ sk_F))))
% 0.20/0.46         != (k2_tarski @ sk_A @ sk_D))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d3_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X9 @ X10 @ X11)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X9 @ X10 @ X11)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.46  thf(t24_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ E ) =>
% 0.20/0.46       ( ( ( E ) =
% 0.20/0.46           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.20/0.46         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.20/0.46           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.46         (((X8) != (k2_tarski @ (k4_tarski @ X4 @ X5) @ (k4_tarski @ X6 @ X7)))
% 0.20/0.46          | ((k1_relat_1 @ X8) = (k2_tarski @ X4 @ X6))
% 0.20/0.46          | ~ (v1_relat_1 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ 
% 0.20/0.46             (k2_tarski @ (k4_tarski @ X4 @ X5) @ (k4_tarski @ X6 @ X7)))
% 0.20/0.46          | ((k1_relat_1 @ 
% 0.20/0.46              (k2_tarski @ (k4_tarski @ X4 @ X5) @ (k4_tarski @ X6 @ X7)))
% 0.20/0.46              = (k2_tarski @ X4 @ X6)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.46  thf(fc7_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( v1_relat_1 @
% 0.20/0.46       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         (v1_relat_1 @ 
% 0.20/0.46          (k2_tarski @ (k4_tarski @ X0 @ X1) @ (k4_tarski @ X2 @ X3)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k1_relat_1 @ 
% 0.20/0.46           (k2_tarski @ (k4_tarski @ X4 @ X5) @ (k4_tarski @ X6 @ X7)))
% 0.20/0.46           = (k2_tarski @ X4 @ X6))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         ((k1_relat_1 @ 
% 0.20/0.46           (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ (k4_tarski @ X3 @ X4)))
% 0.20/0.46           = (k2_tarski @ (k4_tarski @ X2 @ X1) @ X3))),
% 0.20/0.46      inference('sup+', [status(thm)], ['2', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         ((k1_relat_1 @ 
% 0.20/0.46           (k2_tarski @ (k3_mcart_1 @ X4 @ X3 @ X5) @ 
% 0.20/0.46            (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.20/0.46           = (k2_tarski @ (k4_tarski @ X4 @ X3) @ (k4_tarski @ X2 @ X1)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k1_relat_1 @ 
% 0.20/0.46           (k2_tarski @ (k4_tarski @ X4 @ X5) @ (k4_tarski @ X6 @ X7)))
% 0.20/0.46           = (k2_tarski @ X4 @ X6))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('10', plain, (((k2_tarski @ sk_A @ sk_D) != (k2_tarski @ sk_A @ sk_D))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '8', '9'])).
% 0.20/0.46  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
