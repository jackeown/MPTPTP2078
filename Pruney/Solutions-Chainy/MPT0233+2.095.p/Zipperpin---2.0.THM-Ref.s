%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z40RejyupX

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  156 ( 208 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X38 ) @ ( k2_tarski @ X38 @ X39 ) )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X41 = X40 )
      | ( X41 = X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('10',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z40RejyupX
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 43 iterations in 0.025s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(t28_zfmisc_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.45          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.45             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t19_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.45       ( k1_tarski @ A ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X38 : $i, X39 : $i]:
% 0.20/0.45         ((k3_xboole_0 @ (k1_tarski @ X38) @ (k2_tarski @ X38 @ X39))
% 0.20/0.45           = (k1_tarski @ X38))),
% 0.20/0.45      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.45  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.45  thf(t17_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.20/0.45      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.45      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 0.20/0.45      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.45  thf(t1_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.45       ( r1_tarski @ A @ C ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.45         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.45          | ~ (r1_tarski @ X8 @ X9)
% 0.20/0.45          | (r1_tarski @ X7 @ X9))),
% 0.20/0.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.20/0.45          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '7'])).
% 0.20/0.45  thf(t25_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.45          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.45         (((X41) = (X40))
% 0.20/0.45          | ((X41) = (X42))
% 0.20/0.45          | ~ (r1_tarski @ (k1_tarski @ X41) @ (k2_tarski @ X40 @ X42)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.45  thf('10', plain, ((((sk_A) = (sk_D)) | ((sk_A) = (sk_C)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain, (((sk_A) != (sk_C))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('12', plain, (((sk_A) != (sk_D))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('13', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['10', '11', '12'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
