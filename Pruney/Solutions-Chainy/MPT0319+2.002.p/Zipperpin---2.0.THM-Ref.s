%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.abuP96Y2Lj

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  290 ( 534 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t131_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( A != B )
       => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) )
          & ( r1_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_zfmisc_1])).

thf('3',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['4','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('20',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.abuP96Y2Lj
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:03:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 38 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(l27_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ X8) @ X9) | (r2_hidden @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.49  thf(t127_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.49       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.21/0.49          | ~ (r1_xboole_0 @ X11 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r2_hidden @ X1 @ X0)
% 0.21/0.49          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.21/0.49             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t131_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( A ) != ( B ) ) =>
% 0.21/0.49       ( ( r1_xboole_0 @
% 0.21/0.49           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.49           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.21/0.49         ( r1_xboole_0 @
% 0.21/0.49           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.49           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( ( A ) != ( B ) ) =>
% 0.21/0.49          ( ( r1_xboole_0 @
% 0.21/0.49              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.21/0.49              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.21/0.49            ( r1_xboole_0 @
% 0.21/0.49              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.21/0.49              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))
% 0.21/0.49        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.49             (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.49           (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.49               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ X8) @ X9) | (r2_hidden @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.21/0.49          | ~ (r1_xboole_0 @ X10 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r2_hidden @ X1 @ X0)
% 0.21/0.49          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X3) @ 
% 0.21/0.49             (k2_zfmisc_1 @ X0 @ X2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf(d1_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X3 : $i]:
% 0.21/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((sk_A) = (sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.49  thf('13', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.49         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))) | 
% 0.21/0.49       ~
% 0.21/0.49       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C_1) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.49         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.49          (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['4', '16'])).
% 0.21/0.49  thf('18', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i, X3 : $i]:
% 0.21/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf('20', plain, (((sk_A) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
