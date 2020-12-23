%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yrIk4OMZYq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  239 ( 296 expanded)
%              Number of equality atoms :   35 (  44 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X21: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ X23 )
        = ( k1_tarski @ X21 ) )
      | ( r2_hidden @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('6',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 != X24 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X24 ) )
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X24 ) )
     != ( k1_tarski @ X24 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X24 ) )
     != ( k1_tarski @ X24 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['6','12'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('15',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yrIk4OMZYq
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:45:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 31 iterations in 0.021s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(t25_zfmisc_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.19/0.46          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.19/0.46             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t28_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.19/0.46         = (k1_tarski @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf(t100_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X1 : $i, X2 : $i]:
% 0.19/0.46         ((k4_xboole_0 @ X1 @ X2)
% 0.19/0.46           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.19/0.46         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf(l33_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.46       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X21 : $i, X23 : $i]:
% 0.19/0.46         (((k4_xboole_0 @ (k1_tarski @ X21) @ X23) = (k1_tarski @ X21))
% 0.19/0.46          | (r2_hidden @ X21 @ X23))),
% 0.19/0.46      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.19/0.46          = (k1_tarski @ sk_A))
% 0.19/0.46        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf(t20_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.46         ( k1_tarski @ A ) ) <=>
% 0.19/0.46       ( ( A ) != ( B ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X24 : $i, X25 : $i]:
% 0.19/0.47         (((X25) != (X24))
% 0.19/0.47          | ((k4_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X24))
% 0.19/0.47              != (k1_tarski @ X25)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X24 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X24))
% 0.19/0.47           != (k1_tarski @ X24))),
% 0.19/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.47  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.47  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X1 : $i, X2 : $i]:
% 0.19/0.47         ((k4_xboole_0 @ X1 @ X2)
% 0.19/0.47           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X24 : $i]:
% 0.19/0.47         ((k5_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X24))
% 0.19/0.47           != (k1_tarski @ X24))),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '11'])).
% 0.19/0.47  thf('13', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 0.19/0.47  thf(d2_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.47       ( ![D:$i]:
% 0.19/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X9 @ X7)
% 0.19/0.47          | ((X9) = (X8))
% 0.19/0.47          | ((X9) = (X5))
% 0.19/0.47          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.19/0.47         (((X9) = (X5))
% 0.19/0.47          | ((X9) = (X8))
% 0.19/0.47          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.47  thf('16', plain, ((((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '15'])).
% 0.19/0.47  thf('17', plain, (((sk_A) != (sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('18', plain, (((sk_A) != (sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('19', plain, ($false),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['16', '17', '18'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
