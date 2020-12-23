%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BhM5TYzRMv

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:14 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 ( 617 expanded)
%              Number of equality atoms :   49 (  74 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','15'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X26 @ X28 ) @ X27 )
        = ( k2_tarski @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_D @ X0 ) @ sk_A )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D @ X0 ) )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_D @ sk_D ) )
    = ( k2_tarski @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['26','36'])).

thf('38',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BhM5TYzRMv
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/1.01  % Solved by: fo/fo7.sh
% 0.77/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.01  % done 1064 iterations in 0.561s
% 0.77/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/1.01  % SZS output start Refutation
% 0.77/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.77/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.77/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.77/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/1.01  thf('0', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf(t148_zfmisc_1, conjecture,
% 0.77/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01     ( ( ( r1_tarski @ A @ B ) & 
% 0.77/1.01         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.77/1.01         ( r2_hidden @ D @ A ) ) =>
% 0.77/1.01       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.77/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01        ( ( ( r1_tarski @ A @ B ) & 
% 0.77/1.01            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.77/1.01            ( r2_hidden @ D @ A ) ) =>
% 0.77/1.01          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.77/1.01    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.77/1.01  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(l32_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/1.01  thf('2', plain,
% 0.77/1.01      (![X6 : $i, X8 : $i]:
% 0.77/1.01         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/1.01  thf(t48_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/1.01  thf('4', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.77/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('5', plain,
% 0.77/1.01      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.77/1.01      inference('sup+', [status(thm)], ['3', '4'])).
% 0.77/1.01  thf('6', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('7', plain,
% 0.77/1.01      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['5', '6'])).
% 0.77/1.01  thf(d10_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/1.01  thf('8', plain,
% 0.77/1.01      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.77/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/1.01  thf('9', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.77/1.01      inference('simplify', [status(thm)], ['8'])).
% 0.77/1.01  thf('10', plain,
% 0.77/1.01      (![X6 : $i, X8 : $i]:
% 0.77/1.01         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['9', '10'])).
% 0.77/1.01  thf('12', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.77/1.01           = (k3_xboole_0 @ X14 @ X15))),
% 0.77/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/1.01  thf('13', plain,
% 0.77/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['11', '12'])).
% 0.77/1.01  thf(idempotence_k3_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/1.01  thf('14', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/1.01  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/1.01  thf('16', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['7', '15'])).
% 0.77/1.01  thf(t16_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.77/1.01       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.77/1.01  thf('17', plain,
% 0.77/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.77/1.01           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.77/1.01  thf('18', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ sk_A @ X0)
% 0.77/1.01           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['16', '17'])).
% 0.77/1.01  thf('19', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ sk_A @ X0)
% 0.77/1.01           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['0', '18'])).
% 0.77/1.01  thf('20', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('21', plain,
% 0.77/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.77/1.01           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.77/1.01  thf('22', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.77/1.01           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['20', '21'])).
% 0.77/1.01  thf('23', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.77/1.01      inference('sup+', [status(thm)], ['19', '22'])).
% 0.77/1.01  thf('24', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('25', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('26', plain,
% 0.77/1.01      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.77/1.01  thf('27', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('28', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(t53_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.77/1.01       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.77/1.01  thf('29', plain,
% 0.77/1.01      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.77/1.01         (~ (r2_hidden @ X26 @ X27)
% 0.77/1.01          | ~ (r2_hidden @ X28 @ X27)
% 0.77/1.01          | ((k3_xboole_0 @ (k2_tarski @ X26 @ X28) @ X27)
% 0.77/1.01              = (k2_tarski @ X26 @ X28)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 0.77/1.01  thf('30', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         (((k3_xboole_0 @ (k2_tarski @ sk_D @ X0) @ sk_A)
% 0.77/1.01            = (k2_tarski @ sk_D @ X0))
% 0.77/1.01          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.77/1.01      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/1.01  thf('31', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('32', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D @ X0))
% 0.77/1.01            = (k2_tarski @ sk_D @ X0))
% 0.77/1.01          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.77/1.01  thf('33', plain,
% 0.77/1.01      (((k3_xboole_0 @ sk_A @ (k2_tarski @ sk_D @ sk_D))
% 0.77/1.01         = (k2_tarski @ sk_D @ sk_D))),
% 0.77/1.01      inference('sup-', [status(thm)], ['27', '32'])).
% 0.77/1.01  thf(t69_enumset1, axiom,
% 0.77/1.01    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.77/1.01  thf('34', plain,
% 0.77/1.01      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.77/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/1.01  thf('35', plain,
% 0.77/1.01      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.77/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/1.01  thf('36', plain,
% 0.77/1.01      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.77/1.01      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.77/1.01  thf('37', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D))),
% 0.77/1.01      inference('sup+', [status(thm)], ['26', '36'])).
% 0.77/1.01  thf('38', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('39', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('40', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.77/1.01      inference('demod', [status(thm)], ['38', '39'])).
% 0.77/1.01  thf('41', plain, ($false),
% 0.77/1.01      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.77/1.01  
% 0.77/1.01  % SZS output end Refutation
% 0.77/1.01  
% 0.77/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
