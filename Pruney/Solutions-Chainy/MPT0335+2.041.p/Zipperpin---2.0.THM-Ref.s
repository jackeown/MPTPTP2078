%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.77QTJCIYnx

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:18 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   58 (  75 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  352 ( 564 expanded)
%              Number of equality atoms :   40 (  65 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('1',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_D @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['14','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['13','32'])).

thf('34',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.77QTJCIYnx
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 384 iterations in 0.215s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(t148_zfmisc_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( r1_tarski @ A @ B ) & 
% 0.45/0.67         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.45/0.67         ( r2_hidden @ D @ A ) ) =>
% 0.45/0.67       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67        ( ( ( r1_tarski @ A @ B ) & 
% 0.45/0.67            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.45/0.67            ( r2_hidden @ D @ A ) ) =>
% 0.45/0.67          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.45/0.67  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t38_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.45/0.67       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.45/0.67         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 0.45/0.67          | ~ (r2_hidden @ X25 @ X26)
% 0.45/0.67          | ~ (r2_hidden @ X23 @ X26))),
% 0.45/0.67      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.67          | (r1_tarski @ (k2_tarski @ X0 @ sk_D) @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_D @ sk_D) @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.67  thf(t69_enumset1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.67  thf('5', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_A)),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf(l32_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X2 : $i, X4 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf(t48_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.45/0.67           = (k3_xboole_0 @ X11 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ k1_xboole_0)
% 0.45/0.67         = (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf(t3_boole, axiom,
% 0.45/0.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.67  thf('11', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.45/0.67      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X2 : $i, X4 : $i]:
% 0.45/0.67         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.67  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.45/0.67           = (k3_xboole_0 @ X11 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('20', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('22', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.45/0.67  thf(t16_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.67       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.45/0.67           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ sk_A @ X0)
% 0.45/0.67           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ sk_A @ X0)
% 0.45/0.67           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['14', '24'])).
% 0.45/0.67  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.45/0.67           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.45/0.67           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.45/0.67      inference('sup+', [status(thm)], ['25', '28'])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.45/0.67  thf('33', plain, (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['13', '32'])).
% 0.45/0.67  thf('34', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.67  thf('36', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.45/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf('37', plain, ($false),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['33', '36'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
