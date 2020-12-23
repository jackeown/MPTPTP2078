%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6TeVTcCNGo

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:30 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  245 ( 348 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t57_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ B )
          & ~ ( r2_hidden @ C @ B )
          & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t57_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ X13 )
        = ( k1_tarski @ X11 ) )
      | ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) )
      | ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6TeVTcCNGo
% 0.16/0.37  % Computer   : n003.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:10:12 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.57  % Solved by: fo/fo7.sh
% 0.24/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.57  % done 152 iterations in 0.092s
% 0.24/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.57  % SZS output start Refutation
% 0.24/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.57  thf(t57_zfmisc_1, conjecture,
% 0.24/0.57    (![A:$i,B:$i,C:$i]:
% 0.24/0.57     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.24/0.57          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.24/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.57        ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.24/0.57             ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ) )),
% 0.24/0.57    inference('cnf.neg', [status(esa)], [t57_zfmisc_1])).
% 0.24/0.57  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf(t69_enumset1, axiom,
% 0.24/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.57  thf('1', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf(l33_zfmisc_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.24/0.57       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.24/0.57  thf('2', plain,
% 0.24/0.57      (![X11 : $i, X13 : $i]:
% 0.24/0.57         (((k4_xboole_0 @ (k1_tarski @ X11) @ X13) = (k1_tarski @ X11))
% 0.24/0.57          | (r2_hidden @ X11 @ X13))),
% 0.24/0.57      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.24/0.57  thf(t79_xboole_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.24/0.57  thf('3', plain,
% 0.24/0.57      (![X6 : $i, X7 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X7)),
% 0.24/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.57  thf(symmetry_r1_xboole_0, axiom,
% 0.24/0.57    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.24/0.57  thf('4', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.24/0.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.24/0.57  thf('5', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.57  thf('6', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.24/0.57      inference('sup+', [status(thm)], ['2', '5'])).
% 0.24/0.57  thf('7', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.24/0.57      inference('sup+', [status(thm)], ['1', '6'])).
% 0.24/0.57  thf('8', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.24/0.57      inference('sup+', [status(thm)], ['2', '5'])).
% 0.24/0.57  thf(t70_xboole_1, axiom,
% 0.24/0.57    (![A:$i,B:$i,C:$i]:
% 0.24/0.57     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.24/0.57            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.24/0.57       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.24/0.57            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.24/0.57  thf('9', plain,
% 0.24/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4))
% 0.24/0.57          | ~ (r1_xboole_0 @ X2 @ X3)
% 0.24/0.57          | ~ (r1_xboole_0 @ X2 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.24/0.57  thf('10', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         ((r2_hidden @ X0 @ X1)
% 0.24/0.57          | ~ (r1_xboole_0 @ X1 @ X2)
% 0.24/0.57          | (r1_xboole_0 @ X1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.57  thf('11', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         ((r2_hidden @ X0 @ X1)
% 0.24/0.57          | (r1_xboole_0 @ X1 @ 
% 0.24/0.57             (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X0 @ X0)))
% 0.24/0.57          | (r2_hidden @ X2 @ X1))),
% 0.24/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.24/0.57  thf('12', plain,
% 0.24/0.57      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf(t41_enumset1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( k2_tarski @ A @ B ) =
% 0.24/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.24/0.57  thf('13', plain,
% 0.24/0.57      (![X8 : $i, X9 : $i]:
% 0.24/0.57         ((k2_tarski @ X8 @ X9)
% 0.24/0.57           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.24/0.57  thf('14', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((k2_tarski @ X1 @ X0)
% 0.24/0.57           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.24/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.24/0.57  thf('15', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         ((r2_hidden @ X0 @ X1)
% 0.24/0.57          | (r1_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))
% 0.24/0.57          | (r2_hidden @ X2 @ X1))),
% 0.24/0.57      inference('demod', [status(thm)], ['11', '14'])).
% 0.24/0.57  thf('16', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.24/0.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.24/0.57  thf('17', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         ((r2_hidden @ X1 @ X2)
% 0.24/0.57          | (r2_hidden @ X0 @ X2)
% 0.24/0.57          | (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.24/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.57  thf('18', plain, (~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('19', plain, (((r2_hidden @ sk_C @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.24/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.57  thf('20', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('21', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.57      inference('clc', [status(thm)], ['19', '20'])).
% 0.24/0.57  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.24/0.57  
% 0.24/0.57  % SZS output end Refutation
% 0.24/0.57  
% 0.24/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
