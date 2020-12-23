%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sJHrchPq1V

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:16 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  387 ( 581 expanded)
%              Number of equality atoms :   42 (  65 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

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

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k4_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 )
      = ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r2_hidden @ X54 @ X53 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X52 @ X54 ) @ X53 )
        = ( k2_tarski @ X52 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_D_1 @ X0 ) @ sk_A )
        = ( k2_tarski @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D_1 @ X0 ) )
        = ( k2_tarski @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_D_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sJHrchPq1V
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:40:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.35/1.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.57  % Solved by: fo/fo7.sh
% 1.35/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.57  % done 2129 iterations in 1.107s
% 1.35/1.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.57  % SZS output start Refutation
% 1.35/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.35/1.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.35/1.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.35/1.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.35/1.57  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.57  thf(commutativity_k3_xboole_0, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.35/1.57  thf('0', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf(t48_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.35/1.57  thf('1', plain,
% 1.35/1.57      (![X22 : $i, X23 : $i]:
% 1.35/1.57         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.35/1.57           = (k3_xboole_0 @ X22 @ X23))),
% 1.35/1.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.35/1.57  thf(t148_zfmisc_1, conjecture,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57     ( ( ( r1_tarski @ A @ B ) & 
% 1.35/1.57         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.35/1.57         ( r2_hidden @ D @ A ) ) =>
% 1.35/1.57       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.35/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57        ( ( ( r1_tarski @ A @ B ) & 
% 1.35/1.57            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.35/1.57            ( r2_hidden @ D @ A ) ) =>
% 1.35/1.57          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.35/1.57    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.35/1.57  thf('2', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t109_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.35/1.57  thf('3', plain,
% 1.35/1.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X10 @ X11)
% 1.35/1.57          | (r1_tarski @ (k4_xboole_0 @ X10 @ X12) @ X11))),
% 1.35/1.57      inference('cnf', [status(esa)], [t109_xboole_1])).
% 1.35/1.57  thf('4', plain,
% 1.35/1.57      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)),
% 1.35/1.57      inference('sup-', [status(thm)], ['2', '3'])).
% 1.35/1.57  thf(t12_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.35/1.57  thf('5', plain,
% 1.35/1.57      (![X13 : $i, X14 : $i]:
% 1.35/1.57         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 1.35/1.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.57  thf('6', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1) = (sk_B_1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['4', '5'])).
% 1.35/1.57  thf(t21_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.35/1.57  thf('7', plain,
% 1.35/1.57      (![X18 : $i, X19 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (X18))),
% 1.35/1.57      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.57  thf('8', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.35/1.57           = (k4_xboole_0 @ sk_A @ X0))),
% 1.35/1.57      inference('sup+', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('9', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf('10', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ X0))
% 1.35/1.57           = (k4_xboole_0 @ sk_A @ X0))),
% 1.35/1.57      inference('demod', [status(thm)], ['8', '9'])).
% 1.35/1.57  thf('11', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_A @ X0))
% 1.35/1.57           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['1', '10'])).
% 1.35/1.57  thf('12', plain,
% 1.35/1.57      (![X22 : $i, X23 : $i]:
% 1.35/1.57         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.35/1.57           = (k3_xboole_0 @ X22 @ X23))),
% 1.35/1.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.35/1.57  thf('13', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_A @ X0))
% 1.35/1.57           = (k3_xboole_0 @ sk_A @ X0))),
% 1.35/1.57      inference('demod', [status(thm)], ['11', '12'])).
% 1.35/1.57  thf('14', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ X0 @ sk_A))
% 1.35/1.57           = (k3_xboole_0 @ sk_A @ X0))),
% 1.35/1.57      inference('sup+', [status(thm)], ['0', '13'])).
% 1.35/1.57  thf('15', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C) = (k1_tarski @ sk_D_1))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t16_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.35/1.57       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.35/1.57  thf('16', plain,
% 1.35/1.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 1.35/1.57           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.35/1.57  thf('17', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)
% 1.35/1.57           = (k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_C @ X0)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['15', '16'])).
% 1.35/1.57  thf('18', plain,
% 1.35/1.57      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A)
% 1.35/1.57         = (k3_xboole_0 @ sk_A @ sk_C))),
% 1.35/1.57      inference('sup+', [status(thm)], ['14', '17'])).
% 1.35/1.57  thf('19', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf('20', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf('21', plain,
% 1.35/1.57      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 1.35/1.57         = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.35/1.57  thf('22', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('23', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t53_zfmisc_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.35/1.57       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 1.35/1.57  thf('24', plain,
% 1.35/1.57      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X52 @ X53)
% 1.35/1.57          | ~ (r2_hidden @ X54 @ X53)
% 1.35/1.57          | ((k3_xboole_0 @ (k2_tarski @ X52 @ X54) @ X53)
% 1.35/1.57              = (k2_tarski @ X52 @ X54)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 1.35/1.57  thf('25', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ (k2_tarski @ sk_D_1 @ X0) @ sk_A)
% 1.35/1.57            = (k2_tarski @ sk_D_1 @ X0))
% 1.35/1.57          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['23', '24'])).
% 1.35/1.57  thf('26', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf('27', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D_1 @ X0))
% 1.35/1.57            = (k2_tarski @ sk_D_1 @ X0))
% 1.35/1.57          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['25', '26'])).
% 1.35/1.57  thf('28', plain,
% 1.35/1.57      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D_1 @ sk_D_1))
% 1.35/1.57         = (k2_tarski @ sk_D_1 @ sk_D_1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['22', '27'])).
% 1.35/1.57  thf(t69_enumset1, axiom,
% 1.35/1.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.35/1.57  thf('29', plain,
% 1.35/1.57      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 1.35/1.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.35/1.57  thf('30', plain,
% 1.35/1.57      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 1.35/1.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.35/1.57  thf('31', plain,
% 1.35/1.57      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 1.35/1.57      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.35/1.57  thf('32', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D_1))),
% 1.35/1.57      inference('sup+', [status(thm)], ['21', '31'])).
% 1.35/1.57  thf('33', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('34', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf('35', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D_1))),
% 1.35/1.57      inference('demod', [status(thm)], ['33', '34'])).
% 1.35/1.57  thf('36', plain, ($false),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 1.35/1.57  
% 1.35/1.57  % SZS output end Refutation
% 1.35/1.57  
% 1.40/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
