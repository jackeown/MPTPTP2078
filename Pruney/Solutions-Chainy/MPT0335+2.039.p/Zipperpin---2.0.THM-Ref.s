%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fg7bQBey96

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  322 ( 502 expanded)
%              Number of equality atoms :   38 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ X23 )
        = X23 )
      | ~ ( r2_hidden @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['8','28'])).

thf('30',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fg7bQBey96
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.60  % Solved by: fo/fo7.sh
% 0.20/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.60  % done 162 iterations in 0.152s
% 0.20/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.60  % SZS output start Refutation
% 0.20/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.60  thf(t148_zfmisc_1, conjecture,
% 0.20/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.60     ( ( ( r1_tarski @ A @ B ) & 
% 0.20/0.60         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.20/0.60         ( r2_hidden @ D @ A ) ) =>
% 0.20/0.60       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.20/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.60        ( ( ( r1_tarski @ A @ B ) & 
% 0.20/0.60            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.20/0.60            ( r2_hidden @ D @ A ) ) =>
% 0.20/0.60          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.20/0.60    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.20/0.60  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(l22_zfmisc_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.60       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.60  thf('1', plain,
% 0.20/0.60      (![X23 : $i, X24 : $i]:
% 0.20/0.60         (((k2_xboole_0 @ (k1_tarski @ X24) @ X23) = (X23))
% 0.20/0.60          | ~ (r2_hidden @ X24 @ X23))),
% 0.20/0.60      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.60  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.60  thf(t7_xboole_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.60  thf('3', plain,
% 0.20/0.60      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.60  thf(t28_xboole_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.60  thf('4', plain,
% 0.20/0.60      (![X5 : $i, X6 : $i]:
% 0.20/0.60         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.60  thf('5', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.20/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.60  thf('6', plain,
% 0.20/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_tarski @ sk_D))),
% 0.20/0.60      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.60  thf('7', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.60  thf('8', plain,
% 0.20/0.60      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.20/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.60  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('10', plain,
% 0.20/0.60      (![X5 : $i, X6 : $i]:
% 0.20/0.60         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.60  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('12', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.60  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.60  thf('14', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.60  thf(t16_xboole_1, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i]:
% 0.20/0.60     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.60       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.60  thf('15', plain,
% 0.20/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.60           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.60  thf('16', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.20/0.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.60      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.60  thf('17', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ sk_A @ X0)
% 0.20/0.60           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.20/0.60      inference('sup+', [status(thm)], ['13', '16'])).
% 0.20/0.60  thf('18', plain,
% 0.20/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.60           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.60  thf('19', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.60  thf('20', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.20/0.60           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.60  thf('21', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ sk_A @ X0)
% 0.20/0.60           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.60  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('23', plain,
% 0.20/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.60           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.60  thf('24', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.20/0.60           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.20/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.60  thf('25', plain,
% 0.20/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.60      inference('sup+', [status(thm)], ['21', '24'])).
% 0.20/0.60  thf('26', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.60  thf('27', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.60  thf('28', plain,
% 0.20/0.60      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.20/0.60      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.60  thf('29', plain, (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.20/0.60      inference('sup+', [status(thm)], ['8', '28'])).
% 0.20/0.60  thf('30', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('31', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.60  thf('32', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.20/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.60  thf('33', plain, ($false),
% 0.20/0.60      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 0.20/0.60  
% 0.20/0.60  % SZS output end Refutation
% 0.20/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
