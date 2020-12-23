%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wADKnZBWR2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 469 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X0 ) ) ) ) ),
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
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( sk_A = sk_B )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_D @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['4','13'])).

thf('15',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wADKnZBWR2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 12 iterations in 0.008s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(t17_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( A ) != ( B ) ) =>
% 0.20/0.45       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)) | ((X4) = (X5)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.20/0.45  thf(t127_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.45       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.45          | ~ (r1_xboole_0 @ X1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.45         (((X1) = (X0))
% 0.20/0.45          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k1_tarski @ X1)) @ 
% 0.20/0.45             (k2_zfmisc_1 @ X2 @ (k1_tarski @ X0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t131_zfmisc_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( ( A ) != ( B ) ) =>
% 0.20/0.45       ( ( r1_xboole_0 @
% 0.20/0.45           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.20/0.45           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.20/0.45         ( r1_xboole_0 @
% 0.20/0.45           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.20/0.45           ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45        ( ( ( A ) != ( B ) ) =>
% 0.20/0.45          ( ( r1_xboole_0 @
% 0.20/0.45              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.20/0.45              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ D ) ) & 
% 0.20/0.45            ( r1_xboole_0 @
% 0.20/0.45              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.20/0.45              ( k2_zfmisc_1 @ D @ ( k1_tarski @ B ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t131_zfmisc_1])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.45           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))
% 0.20/0.45        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45             (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45           (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))
% 0.20/0.45         <= (~
% 0.20/0.45             ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45               (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))))),
% 0.20/0.45      inference('split', [status(esa)], ['3'])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)) | ((X4) = (X5)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ (k2_zfmisc_1 @ X2 @ X3))
% 0.20/0.45          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.45         (((X1) = (X0))
% 0.20/0.45          | (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X3) @ 
% 0.20/0.45             (k2_zfmisc_1 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.45           (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))
% 0.20/0.45         <= (~
% 0.20/0.45             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.45               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.20/0.45      inference('split', [status(esa)], ['3'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      ((((sk_A) = (sk_B)))
% 0.20/0.45         <= (~
% 0.20/0.45             ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.45               (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.45  thf('10', plain, (((sk_A) != (sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.45         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (~
% 0.20/0.45       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))) | 
% 0.20/0.45       ~
% 0.20/0.45       ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 0.20/0.45         (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.20/0.45      inference('split', [status(esa)], ['3'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (~
% 0.20/0.45       ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45         (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B))))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45          (k2_zfmisc_1 @ sk_D @ (k1_tarski @ sk_B)))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['4', '13'])).
% 0.20/0.45  thf('15', plain, (((sk_A) = (sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '14'])).
% 0.20/0.45  thf('16', plain, (((sk_A) != (sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('17', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
