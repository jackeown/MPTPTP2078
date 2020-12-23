%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WjsGpNEG44

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 119 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  383 ( 888 expanded)
%              Number of equality atoms :   31 (  72 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X17 ) @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X17 ) @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) )
      = ( k3_tarski @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ X0 )
      = ( k3_tarski @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WjsGpNEG44
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 94 iterations in 0.050s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(t99_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.50  thf('0', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_A)) != (sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t94_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.21/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X17) @ X18)
% 0.21/0.50          | (r2_hidden @ (sk_C_1 @ X18 @ X17) @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.50  thf(d1_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X11 @ X10)
% 0.21/0.50          | (r1_tarski @ X11 @ X9)
% 0.21/0.50          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X9 : $i, X11 : $i]:
% 0.21/0.50         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1)
% 0.21/0.50          | (r1_tarski @ (sk_C_1 @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X17) @ X18)
% 0.21/0.50          | ~ (r1_tarski @ (sk_C_1 @ X18 @ X17) @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.21/0.50          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i]: (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.21/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.50  thf(t12_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0) = (X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf(commutativity_k2_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.50  thf(l51_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0))) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X15 @ X16)) = (k2_xboole_0 @ X15 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X17) @ X18)
% 0.21/0.50          | (r2_hidden @ (sk_C_1 @ X18 @ X17) @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.50  thf(l49_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         ((r1_tarski @ X13 @ (k3_tarski @ X14)) | ~ (r2_hidden @ X13 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.50          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X17) @ X18)
% 0.21/0.50          | ~ (r1_tarski @ (sk_C_1 @ X18 @ X17) @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ X0))
% 0.21/0.50          | (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]: (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X8 @ X9)
% 0.21/0.50          | (r2_hidden @ X8 @ X10)
% 0.21/0.50          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (r2_hidden @ (k3_tarski @ X0) @ (k1_zfmisc_1 @ (k3_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         ((r1_tarski @ X13 @ (k3_tarski @ X14)) | ~ (r2_hidden @ X13 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (r1_tarski @ (k3_tarski @ X0) @ 
% 0.21/0.50          (k3_tarski @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k3_tarski @ X0) @ 
% 0.21/0.50           (k3_tarski @ (k1_zfmisc_1 @ (k3_tarski @ X0))))
% 0.21/0.50           = (k3_tarski @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0))) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k3_tarski @ X0) = (k3_tarski @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.21/0.50           = (k3_tarski @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['16', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X0 @ X1)
% 0.21/0.50           = (k3_tarski @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.21/0.50           = (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['15', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 0.21/0.50           = (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0))) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.50  thf('39', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, (((sk_A) != (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '39'])).
% 0.21/0.50  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
