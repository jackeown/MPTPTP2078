%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RgUhZ2gRe

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  343 ( 444 expanded)
%              Number of equality atoms :   43 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X24 @ ( k1_tarski @ X23 ) )
        = ( k1_tarski @ X23 ) )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X24 @ ( k1_tarski @ X23 ) )
        = ( k1_tarski @ X23 ) )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( ( k3_xboole_0 @ X22 @ ( k1_tarski @ X21 ) )
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_C @ ( k2_tarski @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_C @ ( k2_tarski @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('25',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RgUhZ2gRe
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:30:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 69 iterations in 0.064s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(t59_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.22/0.52          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.52        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.22/0.52             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf(d2_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.52       ( ![D:$i]:
% 0.22/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.52         (((X6) != (X5))
% 0.22/0.52          | (r2_hidden @ X6 @ X7)
% 0.22/0.52          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 0.22/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.52  thf(l31_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.52       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X24 @ (k1_tarski @ X23)) = (k1_tarski @ X23))
% 0.22/0.52          | ~ (r2_hidden @ X23 @ X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.22/0.52           = (k1_tarski @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.22/0.52           = (k1_tarski @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.52  thf('10', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X24 @ (k1_tarski @ X23)) = (k1_tarski @ X23))
% 0.22/0.52          | ~ (r2_hidden @ X23 @ X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf(t16_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.52       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.22/0.52           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.22/0.52  thf(l29_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.22/0.52       ( r2_hidden @ B @ A ) ))).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X21 : $i, X22 : $i]:
% 0.22/0.52         ((r2_hidden @ X21 @ X22)
% 0.22/0.52          | ((k3_xboole_0 @ X22 @ (k1_tarski @ X21)) != (k1_tarski @ X21)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.22/0.52            != (k1_tarski @ X0))
% 0.22/0.52          | (r2_hidden @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)) != (k1_tarski @ sk_B))
% 0.22/0.52          | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ (k1_tarski @ sk_B) @ X0) != (k1_tarski @ sk_B))
% 0.22/0.52          | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.22/0.52          | (r2_hidden @ sk_B @ (k3_xboole_0 @ (k2_tarski @ X0 @ sk_B) @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.22/0.52          | (r2_hidden @ sk_B @ (k3_xboole_0 @ sk_C @ (k2_tarski @ X0 @ sk_B))))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (r2_hidden @ sk_B @ (k3_xboole_0 @ sk_C @ (k2_tarski @ X0 @ sk_B)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.52  thf('22', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '21'])).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X9 @ X7)
% 0.22/0.52          | ((X9) = (X8))
% 0.22/0.52          | ((X9) = (X5))
% 0.22/0.52          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (((X9) = (X5))
% 0.22/0.52          | ((X9) = (X8))
% 0.22/0.52          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.52  thf('28', plain, (((sk_B) = (sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '27'])).
% 0.22/0.52  thf('29', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
