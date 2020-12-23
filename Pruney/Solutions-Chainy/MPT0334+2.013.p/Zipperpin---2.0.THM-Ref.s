%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJBwsDgRwb

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  192 ( 235 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X2 ) @ X3 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X3 ) @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ ( k1_tarski @ X0 ) )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('3',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJBwsDgRwb
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 12 iterations in 0.012s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(t17_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( A ) != ( B ) ) =>
% 0.20/0.45       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X8 : $i, X9 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)) | ((X8) = (X9)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.20/0.45  thf(t87_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.45       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 0.20/0.45         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ X2 @ X3)
% 0.20/0.45          | ((k2_xboole_0 @ (k4_xboole_0 @ X4 @ X2) @ X3)
% 0.20/0.45              = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X3) @ X2)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t87_xboole_1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (((X1) = (X0))
% 0.20/0.45          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ 
% 0.20/0.45              (k1_tarski @ X0))
% 0.20/0.45              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k1_tarski @ X0)) @ 
% 0.20/0.45                 (k1_tarski @ X1))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t147_zfmisc_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( A ) != ( B ) ) =>
% 0.20/0.45       ( ( k4_xboole_0 @
% 0.20/0.45           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.20/0.45         ( k2_xboole_0 @
% 0.20/0.45           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( ( A ) != ( B ) ) =>
% 0.20/0.45          ( ( k4_xboole_0 @
% 0.20/0.45              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.20/0.45            ( k2_xboole_0 @
% 0.20/0.45              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45         (k1_tarski @ sk_B))
% 0.20/0.45         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 0.20/0.45             (k1_tarski @ sk_A)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 0.20/0.45         (k1_tarski @ sk_B))
% 0.20/0.45         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.20/0.45             (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))),
% 0.20/0.45      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 0.20/0.45          (k1_tarski @ sk_A))
% 0.20/0.45          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.20/0.45              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 0.20/0.45        | ((sk_B) = (sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.20/0.45          (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)))
% 0.20/0.45          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.20/0.45              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 0.20/0.45        | ((sk_B) = (sk_A)))),
% 0.20/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain, (((sk_B) = (sk_A))),
% 0.20/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.45  thf('10', plain, (((sk_A) != (sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('11', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
