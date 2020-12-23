%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QFZN4i9pAx

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  201 ( 264 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t23_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X9 ) )
        = ( k1_tarski @ X8 ) )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_B = sk_A ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_tarski @ sk_B )
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X4 @ X6 ) @ X5 )
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ( k1_tarski @ sk_B )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QFZN4i9pAx
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 23 iterations in 0.030s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(commutativity_k2_tarski, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.44  thf(t23_zfmisc_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( A ) != ( B ) ) =>
% 0.20/0.44       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.20/0.44         ( k1_tarski @ A ) ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X8 : $i, X9 : $i]:
% 0.20/0.44         (((k4_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X9))
% 0.20/0.44            = (k1_tarski @ X8))
% 0.20/0.44          | ((X8) = (X9)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t23_zfmisc_1])).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.20/0.44            = (k1_tarski @ X0))
% 0.20/0.44          | ((X0) = (X1)))),
% 0.20/0.44      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.44  thf(t59_zfmisc_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.20/0.44          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.44        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.20/0.44             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t47_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.44           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A))
% 0.20/0.44         = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.44      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      ((((k1_tarski @ sk_B) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.44        | ((sk_B) = (sk_A)))),
% 0.20/0.44      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.44  thf('7', plain, (((sk_A) != (sk_B))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (((k1_tarski @ sk_B) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.44      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.44  thf(l38_zfmisc_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.44       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.20/0.44         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.44          | ((k4_xboole_0 @ (k2_tarski @ X4 @ X6) @ X5) != (k1_tarski @ X4)))),
% 0.20/0.44      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) != (k1_tarski @ X0))
% 0.20/0.44          | ~ (r2_hidden @ X0 @ X2))),
% 0.20/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.20/0.44        | ~ (r2_hidden @ sk_B @ sk_C))),
% 0.20/0.44      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.44  thf('13', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('14', plain, (((k1_tarski @ sk_B) != (k1_tarski @ sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
