%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y76y0W91M0

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  169 ( 200 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k1_tarski @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('13',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y76y0W91M0
% 0.14/0.36  % Computer   : n009.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:23:41 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.47  % Solved by: fo/fo7.sh
% 0.23/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.47  % done 40 iterations in 0.017s
% 0.23/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.47  % SZS output start Refutation
% 0.23/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.47  thf(t63_zfmisc_1, conjecture,
% 0.23/0.47    (![A:$i,B:$i,C:$i]:
% 0.23/0.47     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.23/0.47       ( r2_hidden @ A @ C ) ))).
% 0.23/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.47        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.23/0.47          ( r2_hidden @ A @ C ) ) )),
% 0.23/0.47    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.23/0.47  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(t22_xboole_1, axiom,
% 0.23/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.23/0.47  thf('1', plain,
% 0.23/0.47      (![X6 : $i, X7 : $i]:
% 0.23/0.47         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.23/0.47      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.23/0.47  thf('2', plain,
% 0.23/0.47      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.23/0.47         = (k2_tarski @ sk_A @ sk_B))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(t31_xboole_1, axiom,
% 0.23/0.47    (![A:$i,B:$i,C:$i]:
% 0.23/0.47     ( r1_tarski @
% 0.23/0.47       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.23/0.47       ( k2_xboole_0 @ B @ C ) ))).
% 0.23/0.47  thf('3', plain,
% 0.23/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.47         (r1_tarski @ 
% 0.23/0.47          (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)) @ 
% 0.23/0.47          (k2_xboole_0 @ X9 @ X10))),
% 0.23/0.47      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.23/0.47  thf('4', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (r1_tarski @ 
% 0.23/0.47          (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.23/0.47           (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)) @ 
% 0.23/0.47          (k2_xboole_0 @ sk_C @ X0))),
% 0.23/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.23/0.47  thf('5', plain,
% 0.23/0.47      (![X6 : $i, X7 : $i]:
% 0.23/0.47         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.23/0.47      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.23/0.47  thf('6', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_C @ X0))),
% 0.23/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.47  thf('7', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.23/0.47      inference('sup+', [status(thm)], ['1', '6'])).
% 0.23/0.47  thf(t41_enumset1, axiom,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( k2_tarski @ A @ B ) =
% 0.23/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.23/0.47  thf('8', plain,
% 0.23/0.47      (![X18 : $i, X19 : $i]:
% 0.23/0.47         ((k2_tarski @ X18 @ X19)
% 0.23/0.47           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.23/0.47      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.23/0.47  thf(t11_xboole_1, axiom,
% 0.23/0.47    (![A:$i,B:$i,C:$i]:
% 0.23/0.47     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.23/0.47  thf('9', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.47         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.23/0.47      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.23/0.47  thf('10', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.47         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.23/0.47          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.23/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.47  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.23/0.47      inference('sup-', [status(thm)], ['7', '10'])).
% 0.23/0.47  thf(t37_zfmisc_1, axiom,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.23/0.47  thf('12', plain,
% 0.23/0.47      (![X23 : $i, X24 : $i]:
% 0.23/0.47         ((r2_hidden @ X23 @ X24) | ~ (r1_tarski @ (k1_tarski @ X23) @ X24))),
% 0.23/0.47      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.23/0.47  thf('13', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.23/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.47  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.23/0.47  
% 0.23/0.47  % SZS output end Refutation
% 0.23/0.47  
% 0.23/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
