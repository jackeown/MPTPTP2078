%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FSGz4FnAqN

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:42 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 ( 297 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t79_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_tarski @ X14 @ X12 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C @ X2 @ ( k1_zfmisc_1 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FSGz4FnAqN
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.77/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.98  % Solved by: fo/fo7.sh
% 0.77/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.98  % done 1278 iterations in 0.557s
% 0.77/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.98  % SZS output start Refutation
% 0.77/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.98  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.77/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.98  thf(t79_zfmisc_1, conjecture,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( r1_tarski @ A @ B ) =>
% 0.77/0.98       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.77/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.98    (~( ![A:$i,B:$i]:
% 0.77/0.98        ( ( r1_tarski @ A @ B ) =>
% 0.77/0.98          ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.77/0.98    inference('cnf.neg', [status(esa)], [t79_zfmisc_1])).
% 0.77/0.98  thf('0', plain,
% 0.77/0.98      (~ (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(t12_xboole_1, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.77/0.98  thf('2', plain,
% 0.77/0.98      (![X7 : $i, X8 : $i]:
% 0.77/0.98         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.77/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.77/0.98  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.77/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.98  thf(commutativity_k2_tarski, axiom,
% 0.77/0.98    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.77/0.98  thf('4', plain,
% 0.77/0.98      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.77/0.98      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.77/0.98  thf(l51_zfmisc_1, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.98  thf('5', plain,
% 0.77/0.98      (![X16 : $i, X17 : $i]:
% 0.77/0.98         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.77/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.98  thf('6', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.98      inference('sup+', [status(thm)], ['4', '5'])).
% 0.77/0.98  thf('7', plain,
% 0.77/0.98      (![X16 : $i, X17 : $i]:
% 0.77/0.98         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.77/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.98  thf('8', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.98      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/0.98  thf(d3_tarski, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( r1_tarski @ A @ B ) <=>
% 0.77/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/0.98  thf('9', plain,
% 0.77/0.98      (![X1 : $i, X3 : $i]:
% 0.77/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.77/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.98  thf(d1_zfmisc_1, axiom,
% 0.77/0.98    (![A:$i,B:$i]:
% 0.77/0.98     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.77/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.77/0.98  thf('10', plain,
% 0.77/0.98      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X14 @ X13)
% 0.77/0.98          | (r1_tarski @ X14 @ X12)
% 0.77/0.98          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.77/0.98      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.77/0.98  thf('11', plain,
% 0.77/0.98      (![X12 : $i, X14 : $i]:
% 0.77/0.98         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 0.77/0.98      inference('simplify', [status(thm)], ['10'])).
% 0.77/0.98  thf('12', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 0.77/0.98          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['9', '11'])).
% 0.77/0.98  thf(t10_xboole_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.77/0.98  thf('13', plain,
% 0.77/0.98      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.77/0.98         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.77/0.98      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.77/0.98  thf('14', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ X1)
% 0.77/0.98          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ 
% 0.77/0.98             (k2_xboole_0 @ X2 @ X0)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.98  thf('15', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.98         ((r1_tarski @ (sk_C @ X2 @ (k1_zfmisc_1 @ X1)) @ 
% 0.77/0.98           (k2_xboole_0 @ X1 @ X0))
% 0.77/0.98          | (r1_tarski @ (k1_zfmisc_1 @ X1) @ X2))),
% 0.77/0.98      inference('sup+', [status(thm)], ['8', '14'])).
% 0.77/0.98  thf('16', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((r1_tarski @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.77/0.98          | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0))),
% 0.77/0.98      inference('sup+', [status(thm)], ['3', '15'])).
% 0.77/0.98  thf('17', plain,
% 0.77/0.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.98         (~ (r1_tarski @ X11 @ X12)
% 0.77/0.98          | (r2_hidden @ X11 @ X13)
% 0.77/0.98          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.77/0.98      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.77/0.98  thf('18', plain,
% 0.77/0.98      (![X11 : $i, X12 : $i]:
% 0.77/0.98         ((r2_hidden @ X11 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X11 @ X12))),
% 0.77/0.98      inference('simplify', [status(thm)], ['17'])).
% 0.77/0.98  thf('19', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ X0)
% 0.77/0.98          | (r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.77/0.98             (k1_zfmisc_1 @ sk_B)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['16', '18'])).
% 0.77/0.98  thf('20', plain,
% 0.77/0.98      (![X1 : $i, X3 : $i]:
% 0.77/0.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.77/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.98  thf('21', plain,
% 0.77/0.98      (((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.77/0.98        | (r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.77/0.98  thf('22', plain, ((r1_tarski @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.77/0.98      inference('simplify', [status(thm)], ['21'])).
% 0.77/0.98  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.77/0.98  
% 0.77/0.98  % SZS output end Refutation
% 0.77/0.98  
% 0.77/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
